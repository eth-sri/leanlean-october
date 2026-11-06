module

public import PottsDiscontinuity.BetheAnsatz.Words

/-!
# Collecting the word coefficients

Pair each L coefficient with the preceding M coefficient. The inclusion-exclusion
sum then factors over cyclic edges, giving ML-1, L, M, or 1 on each edge.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Reindex a product of restricted letters into independent cyclic edge factors. -/
theorem cyclic_restricted_product (e : Equiv.Perm ι) (w : ι → Bool) (l m : ι → ℂ) (S : Finset ι) :
    (∏ k, if w k then (if k ∈ S then 0 else if e.symm k ∈ S then 1 else l k)
      else (if e.symm k ∈ S then 0 else if k ∈ S then 1 else m k)) =
      ∏ k, if k ∈ S then (if w k then 0 else if w (e k) then 1 else 0)
        else (if w (e k) then l (e k) else 1) * (if w k then 1 else m k) := by
  let f := fun k => if w k then (if e.symm k ∈ S then 1 else l k)
    else (if e.symm k ∈ S then 0 else 1)
  let g := fun k => if w k then (if k ∈ S then 0 else 1)
    else (if k ∈ S then 1 else m k)
  have hlocal : ∀ k, (if w k then (if k ∈ S then 0 else if e.symm k ∈ S then 1 else l k)
      else (if e.symm k ∈ S then 0 else if k ∈ S then 1 else m k)) = f k * g k := by
    grind
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, ← Equiv.prod_comp e f, ← Finset.prod_mul_distrib]
  grind

/-- Inclusion-exclusion of coordinate products is a product of differences. -/
theorem sum_powerset_product_choice (f g : ι → ℂ) :
    (∑ S ∈ (univ : Finset ι).powerset, (-1 : ℂ) ^ S.card *
      ∏ k, if k ∈ S then g k else f k) = ∏ k, (f k - g k) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_ite]
  have h1 : (univ : Finset ι).filter (fun k => k ∈ S) = S := by simp
  have h2 : (univ : Finset ι).filter (fun k => k ∉ S) = univ \ S := by grind
  grind
end

section
variable {n : ℕ} (c : ℝ) (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool)
/-- Source coefficient rσ(w), as a product over cyclic edges.
LL contributes the L at the right endpoint; MM contributes the M at the left. -/
noncomputable def wordCoefficient  : ℂ :=
  ∏ k, if w k then
    (if w (finRotate (n + 1) k) then L c (z (p (σ (finRotate (n + 1) k)))) else 1)
  else (if w (finRotate (n + 1) k) then
    M c (z (p (σ k))) * L c (z (p (σ (finRotate (n + 1) k)))) - 1
    else M c (z (p (σ k))))

/-- The inclusion-exclusion coefficient equals the explicit cyclic ML/LL/MM product. -/
theorem inclusionWordCoefficient_eq_wordCoefficient  :
    inclusionWordCoefficient c p σ w = wordCoefficient c p σ w := by
  unfold inclusionWordCoefficient restrictedWordCoefficient restrictedLetterCoefficient
  simp_rw [cyclic_restricted_product (finRotate (n + 1)) w
    (fun k => L c (z (p (σ k)))) (fun k => M c (z (p (σ k))))]
  rw [sum_powerset_product_choice]
  unfold wordCoefficient
  grind
end

/-- Companion Lemma `lem:1`: the exact finite word encoding of the cyclic gap sum. -/
theorem cyclicGapSum_eq_sum_words {N n : ℕ} (c : ℝ) (x : Fin (n + 2) → ℤ)
    (p : Fin (n + 2) → ℝ) (σ : Equiv.Perm (Fin (n + 2))) (hx : StrictMono x)
    (hspan : x (Fin.last (n + 1)) - x 0 < (N : ℤ)) (hp : ∀ j, z (p j) ≠ 1) :
    cyclicGapSum c N x p σ =
      ∑ w : Fin (n + 2) → Bool,
        wordCoefficient c p σ w * wordPhase (N := N) x p σ w := by
  rw [cyclicGapSum_eq_sum_words_uncollected c x p σ hx hspan hp]
  simp_rw [inclusionWordCoefficient_eq_wordCoefficient]

end PottsDiscontinuity.BetheAnsatz
