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

/-- Reindex a product of restricted letters into independent cyclic edge factors. -/
theorem cyclic_restricted_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) (w : ι → Bool) (B : ℂ) (l m : ι → ℂ) (S : Finset ι) :
    (∏ k, if w k then (if k ∈ S then 0 else if e.symm k ∈ S then 1 else l k)
      else (if e.symm k ∈ S then 0 else if k ∈ S then B else m k)) =
      ∏ k, if k ∈ S then (if w k then 0 else if w (e k) then B else 0)
        else (if w (e k) then l (e k) else 1) * (if w k then 1 else m k) := by
  let f : ι → ℂ := fun k => if w k then (if e.symm k ∈ S then 1 else l k)
    else (if e.symm k ∈ S then 0 else 1)
  let g : ι → ℂ := fun k => if w k then (if k ∈ S then 0 else 1)
    else (if k ∈ S then B else m k)
  have hlocal : ∀ k, (if w k then (if k ∈ S then 0 else if e.symm k ∈ S then 1 else l k)
      else (if e.symm k ∈ S then 0 else if k ∈ S then B else m k)) = f k * g k := by
    intro k
    cases hw : w k <;> by_cases hk : k ∈ S <;> by_cases hl : e.symm k ∈ S <;>
      simp only [f, g, hw, hk, hl, Bool.false_eq_true, ↓reduceIte, zero_mul, mul_zero,
        one_mul, mul_one]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, ← Equiv.prod_comp e f, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  dsimp only [f, g]
  rw [e.symm_apply_apply]
  cases hk : w k <;> cases hn : w (e k) <;> by_cases hs : k ∈ S <;>
    simp only [hs, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_mul, one_mul, mul_one]

/-- Inclusion-exclusion of coordinate products is a product of differences. -/
theorem sum_powerset_product_choice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℂ) :
    (∑ S ∈ (univ : Finset ι).powerset, (-1 : ℂ) ^ S.card *
      ∏ k, if k ∈ S then g k else f k) = ∏ k, (f k - g k) := by
  rw [Finset.prod_sub]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_ite]
  have h1 : (univ : Finset ι).filter (fun k => k ∈ S) = S := by simp
  have h2 : (univ : Finset ι).filter (fun k => k ∉ S) = univ \ S := by ext k; simp
  rw [h1, h2]
  ring

/-- Single-letter weights and the common product of forced endpoint weights
at a collision. -/
structure WordWeights (n : ℕ) where
  left : Fin (n+1) → ℂ
  right : Fin (n+1) → ℂ
  collision : ℂ

noncomputable def gapWordWeights {n : ℕ} (B D : ℂ) (p : Fin (n+1) → ℝ) : WordWeights n :=
  ⟨fun j => gapLeft D (z (p j)), fun j => gapRight B D (z (p j)), B⟩

section
variable {n : ℕ} (r : WordWeights n) (σ : Equiv.Perm (Fin (n+1))) (w : Fin (n+1) → Bool)

/-- At ML, subtract the double occupancy at the shared endpoint. -/
noncomputable def wordEdgeFactor (k : Fin (n+1)) : ℂ :=
  let l := finRotate (n+1) k
  if w k then (if w l then r.left (σ l) else 1)
  else if w l then r.right (σ k) * r.left (σ l) - r.collision else r.right (σ k)

noncomputable def wordCoefficient : ℂ := ∏ k, wordEdgeFactor r σ w k
end

/-- Inclusion-exclusion collects into independent cyclic edge factors. -/
theorem inclusionWordCoefficient_eq_wordCoefficient {n : ℕ} (B D : ℂ) (p : Fin (n+1) → ℝ)
    (σ : Equiv.Perm (Fin (n+1))) (w : Fin (n+1) → Bool) :
    inclusionWordCoefficient B D p σ w = wordCoefficient (gapWordWeights B D p) σ w := by
  unfold inclusionWordCoefficient restrictedWordCoefficient restrictedLetterCoefficient
  simp_rw [cyclic_restricted_product (finRotate (n+1)) w B
    (fun k => gapLeft D (z (p (σ k)))) (fun k => gapRight B D (z (p (σ k))))]
  rw [sum_powerset_product_choice]
  unfold wordCoefficient
  apply Finset.prod_congr rfl
  intro k _
  cases hk : w k <;> cases hn : w (finRotate (n+1) k) <;>
    simp only [wordEdgeFactor, gapWordWeights, hk, hn, ite_true, Bool.false_eq_true, ite_false] <;> ring

theorem weightedGapSum_eq_sum_words {N n : ℕ} (B D : ℂ) (x : Fin (n+2) → ℤ)
    (p : Fin (n+2) → ℝ) (σ : Equiv.Perm (Fin (n+2))) (hx : StrictMono x)
    (hspan : x (Fin.last (n+1)) - x 0 < (N : ℤ)) (hp : ∀ j, z (p j) ≠ 1) :
    weightedGapSum (N := N) B D x p σ = ∑ w : Fin (n+2) → Bool,
      wordCoefficient (gapWordWeights B D p) σ w * wordPhase (N := N) x p σ w := by
  rw [weightedGapSum_eq_sum_words_uncollected B D x p σ hx hspan hp]
  simp_rw [inclusionWordCoefficient_eq_wordCoefficient]

end PottsDiscontinuity.BetheAnsatz
