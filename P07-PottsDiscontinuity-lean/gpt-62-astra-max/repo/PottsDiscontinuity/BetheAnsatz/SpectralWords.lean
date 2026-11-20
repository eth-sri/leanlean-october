module
public import PottsDiscontinuity.BetheAnsatz.SpectralWeights
public import PottsDiscontinuity.BetheAnsatz.GapInclusionExclusion

/-! # Endpoint expansion of a row

Inclusion-exclusion pairs every forced right endpoint with the following
forced left endpoint. Their weights multiply to one for every `v ≠ 0`.
The resulting cyclic edge coefficient is therefore still `M L - 1`.
-/
@[expose] public section
open Finset Complex Classical
namespace PottsDiscontinuity.BetheAnsatz
noncomputable section

section
variable {ι : Type*}

/-- Reindex a product of restricted letters into independent cyclic edge factors. -/
theorem cyclic_restricted_product [Fintype ι] [DecidableEq ι]
    {v : ℂ} (hv : v ≠ 0) (e : Equiv.Perm ι) (w : ι → Bool) (l m : ι → ℂ) (S : Finset ι) :
    (∏ k, if w k then (if k ∈ S then 0 else if e.symm k ∈ S then v⁻¹ else l k)
      else (if e.symm k ∈ S then 0 else if k ∈ S then v else m k)) =
      ∏ k, if k ∈ S then (if w k then 0 else if w (e k) then 1 else 0)
        else (if w (e k) then l (e k) else 1) * (if w k then 1 else m k) := by
  let f := fun k => if w k then (if e.symm k ∈ S then v⁻¹ else l k)
    else (if e.symm k ∈ S then 0 else 1)
  have hlocal : ∀ k, (if w k then (if k ∈ S then 0 else if e.symm k ∈ S then v⁻¹ else l k)
      else (if e.symm k ∈ S then 0 else if k ∈ S then v else m k)) = f k * (fun k => if w k then (if k ∈ S then 0 else 1) else (if k ∈ S then v else m k)) k := by
    grind
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, ← Equiv.prod_comp e f, ← Finset.prod_mul_distrib]
  grind

/-- Inclusion-exclusion of coordinate products is a product of differences. -/
theorem sum_powerset_product_choice [Fintype ι] [DecidableEq ι]
    (f g : ι → ℂ) :
    (∑ S ∈ (univ : Finset ι).powerset, (-1) ^ S.card *
      ∏ k, if k ∈ S then g k else f k) = ∏ k, (f k - g k) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_ite]
  have h1 : univ.filter (fun k => k ∈ S) = S := by simp
  have h2 : univ.filter (fun k => k ∉ S) = univ \ S := by grind
  grind

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def restrictedLetter (v : ℂ) (e : Equiv.Perm ι) (l m : ι → ℂ) (S : Finset ι) (k : ι) (b : Bool) : ℂ :=
  if b then (if k ∈ S then 0 else if e.symm k ∈ S then v⁻¹ else l k)
  else (if e.symm k ∈ S then 0 else if k ∈ S then v else m k)

variable {v : ℂ} (hv : v ≠ 0) (e : Equiv.Perm ι) (l m : ι → ℂ)
include e l m

def wordEdgeFactor (w : ι → Bool) (k : ι) : ℂ :=
  if w k then (if w (e k) then l (e k) else 1)
  else if w (e k) then m k * l (e k) - 1 else m k

include hv in
theorem expand_row (P : ι → Bool → ℂ) :
    (∑ S ∈ (univ : Finset ι).powerset, (-1)^S.card *
      ∏ k, ∑ b, restrictedLetter v e l m S k b * P k b) =
    ∑ w, (∏ k, wordEdgeFactor e l m w k) * ∏ k, P k (w k) := by
  simp_rw [Fintype.prod_sum, prod_mul_distrib, mul_sum]; rw [sum_comm]
  apply sum_congr rfl; intro w _
  simp_rw [← mul_assoc, ← sum_mul, restrictedLetter, cyclic_restricted_product hv, sum_powerset_product_choice]
  congr 1; apply prod_congr rfl; intro k _
  cases hw : w k <;> cases hn : w (e k) <;> simp [wordEdgeFactor, hw, hn, mul_comm]
end

variable {N n : ℕ}

section
variable (Δ v : ℂ) (N : ℕ) (x : Fin (n+1) → ℤ) (l m : Fin (n+1) → ℂ) (p : Fin (n+1) → ℝ)
    (σ : Equiv.Perm (Fin (n+1))) (w : Fin (n+1) → Bool)

include N x w in
def wordPositions (k : Fin (n+1)) :=
  if w k then cyclicPredecessorPositions N x k else x k

include l m σ w in
def wordCoefficient :=
  ∏ k, wordEdgeFactor (finRotate _) (l ∘ σ) (m ∘ σ) w k

def gauge (v : ℂ) (x y : Fin n → ℤ) := ∏ k, v^(x k-y k)

def rowKernel (Δ v u : ℂ) (a b k : ℤ) := v^b * (rowEntry Δ v a b k * (u/v)^k)

include Δ v N x p σ in
def spectralGap :=
  ∑ y ∈ distinctGapTuples N x, ∏ k, rowKernel Δ v (z (p (σ k))) (cyclicPredecessorPositions N x k) (x k) (y k)

end

lemma planeWave_powers (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (x : Fin n → ℤ) :
    planeWave p σ x = ∏ k, z (p (σ k))^(x k) := by
  simp only [planeWave, z, ← exp_int_mul]; congr 1; funext k; ring

private lemma row_constrained {v Δ u : ℂ} (hv : v ≠ 0) (hu : u ≠ 0) (hne : u ≠ v) {a b : ℤ} (hab : a < b)
    (A B : Prop) [Decidable A] [Decidable B] :
    (∑ k ∈ (Icc a b).filter (fun k => (A → k = b) ∧ (B → k = a)), rowKernel Δ v u a b k) =
      (if A then 0 else if B then v⁻¹ else rowL Δ v u) * (v^(b-a) * u^a) +
      (if B then 0 else if A then v else rowM Δ v u) * (v^(b-b) * u^b) := by
  have h (k : ℤ) : v^b * (u/v)^k = v^(b-k) * u^k := by rw [div_zpow, zpow_sub₀ hv]; ring
  simp only [rowKernel, ← mul_sum]
  by_cases hA : A <;> by_cases hB : B
  · have he : (Icc a b).filter (fun k => (A → k=b) ∧ (B → k=a)) = ∅ := by grind
    grind
  · have he : (Icc a b).filter (fun k => (A → k=b) ∧ (B → k=a)) = {b} := by grind
    rw [he]; simp only [sum_singleton, rowEntry, hab.ne', ite_false, ite_true, hA, hB, not_false_eq_true, ↓reduceIte, zero_mul, zero_add]; grind
  · have he : (Icc a b).filter (fun k => (A → k=b) ∧ (B → k=a)) = {a} := by grind
    rw [he]; simp only [sum_singleton, rowEntry, ↓reduceIte, hA, hB, zero_mul, add_zero]; grind
  · simp only [hA,hB,false_implies, and_self, filter_true, ↓reduceIte, row_gap hv hu hne hab, mul_add]; grind

lemma spectralGap_words {Δ v : ℂ} (hv : v ≠ 0) (x : Fin (n+2) → ℤ) (hx : StrictMono x)
    (hspan : x (Fin.last (n+1)) - x 0 < N) (p : Fin (n+2) → ℝ) (hp : ∀ j, z (p j) ≠ v)
    (σ : Equiv.Perm (Fin (n+2))) :
    spectralGap Δ v N x p σ = ∑ w, wordCoefficient (fun j => rowL Δ v (z (p j))) (fun j => rowM Δ v (z (p j))) σ w *
        (gauge v x (wordPositions N x w) * planeWave p σ (wordPositions N x w)) := by
  let a := cyclicPredecessorPositions N x
  let K := fun k y => rowKernel Δ v (z (p (σ k))) (a k) (x k) y
  let P := fun k (b : Bool) => v^(x k - (if b then a k else x k)) * z (p (σ k))^(if b then a k else x k)
  have he : distinctGapTuples N x = (gapTuples N x).filter (fun y => ∀ k, ¬gapCollision N x y k) := by
    ext y; simp only [distinctGapTuples, mem_filter]; exact and_congr_right fun h => distinct_residues_iff_no_gapCollision hx hspan h
  calc
    _ = ∑ S ∈ univ.powerset, (-1)^S.card *
        ∑ y ∈ (gapTuples N x).filter (fun y => ∀ k ∈ S, gapCollision N x y k), ∏ k, K k (y k) := by
      unfold spectralGap; rw [he]
      convert! sum_no_events_eq_powerset (gapTuples N x) (fun k y => gapCollision N x y k) (fun y => ∏ k, K k (y k)) using 1
      · exact sum_congr (by ext; simp) fun _ _ => rfl
      · apply sum_congr rfl; intro S _; congr 1; exact sum_congr (by ext; simp) fun _ _ => rfl
    _ = ∑ S ∈ univ.powerset, (-1)^S.card * ∏ k, ∑ b, restrictedLetter v (finRotate (n+2)) (fun k => rowL Δ v (z (p (σ k)))) (fun k => rowM Δ v (z (p (σ k)))) S k b * P k b := by
      apply sum_congr rfl; intro S _; congr 1; rw [restricted_gapTuples_eq_pi, ← prod_univ_sum _ K]
      apply prod_congr rfl; intro k _; rw [Fintype.sum_bool]
      exact row_constrained hv (z_ne_zero _) (hp _) (cyclicPredecessorPositions_lt hx hspan k) _ _
    _ = _ := by rw [expand_row hv]; apply sum_congr rfl; intro w _; simp only [P,wordPositions,planeWave_powers,gauge,prod_mul_distrib,a]; rfl

end
end PottsDiscontinuity.BetheAnsatz
