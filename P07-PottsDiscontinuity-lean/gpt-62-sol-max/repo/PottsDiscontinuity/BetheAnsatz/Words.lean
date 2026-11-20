module

public import PottsDiscontinuity.BetheAnsatz.GapRestricted

/-!
# Words in the restricted gap expansion

A true letter denotes L and a false letter denotes M. We first keep the collision
set visible in each coefficient. Summing these coefficients by inclusion-exclusion
is an exact word expansion before the coefficient is collected into ML factors.
-/

@[expose] public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

def wordPositions {n : ℕ} (N : ℕ) (x : Fin (n+1) → ℤ) (w : Fin (n+1) → Bool) :
    Fin (n+1) → ℤ := fun k => if w k then cyclicPredecessorPositions N x k else x k

/-- Endpoint phase of a word, in the integer predecessor convention. -/
noncomputable def wordPhase {N n : ℕ} (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  planeWave p σ (wordPositions N x w)

/-- Local coefficient with the two endpoint constraints recorded explicitly. -/
noncomputable def restrictedLetterCoefficient {n : ℕ} (B D : ℂ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (k : Fin (n + 1)) (b : Bool) : ℂ :=
  if b then (if k ∈ S then 0 else
    if (finRotate (n + 1)).symm k ∈ S then 1 else gapLeft D (z (p (σ k))))
  else (if (finRotate (n + 1)).symm k ∈ S then 0 else
    if k ∈ S then B else gapRight B D (z (p (σ k))))

/-- Coefficient of a word before the sum over collision sets. -/
noncomputable def restrictedWordCoefficient {n : ℕ} (B D : ℂ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  ∏ k, restrictedLetterCoefficient B D p σ S k (w k)

/-- The restricted geometric product expanded over all words. -/
theorem restrictedGapSum_eq_sum_words {N n : ℕ} (B D : ℂ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (hx : StrictMono x)
    (hspan : x (Fin.last n) - x 0 < (N : ℤ)) (hp : ∀ j, z (p j) ≠ 1) :
    restrictedGapSum (N := N) B D x p σ S =
      ∑ w : Fin (n + 1) → Bool,
        restrictedWordCoefficient B D p σ S w * wordPhase (N := N) x p σ w := by
  rw [restrictedGapSum_eq_product B D x p σ S hx hspan hp]
  unfold restrictedWordCoefficient wordPhase planeWave wordPositions
  simp_rw [← Finset.prod_mul_distrib]
  change _ = ∑ w : Fin (n+1) → Bool, ∏ k, restrictedLetterCoefficient B D p σ S k (w k) *
    positionPhase (p (σ k)) (if w k then cyclicPredecessorPositions N x k else x k)
  rw [← Fintype.prod_sum (fun k (b : Bool) => restrictedLetterCoefficient B D p σ S k b *
    positionPhase (p (σ k)) (if b then cyclicPredecessorPositions N x k else x k))]
  apply Finset.prod_congr rfl
  intro k _
  simp only [Fintype.sum_bool, restrictedLetterCoefficient, Bool.false_eq_true,
    ↓reduceIte]
  by_cases hk : k ∈ S <;> by_cases hl : (finRotate (n + 1)).symm k ∈ S <;>
    simp_all

/-- Exact inclusion-exclusion coefficient, prior to collecting the ML factors. -/
noncomputable def inclusionWordCoefficient {n : ℕ} (B D : ℂ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1))) (w : Fin (n + 1) → Bool) : ℂ :=
  ∑ S ∈ (univ : Finset (Fin (n + 1))).powerset,
    (-1 : ℂ) ^ S.card * restrictedWordCoefficient B D p σ S w

/-- The finite gap sum expanded in words, with the exact uncollected coefficients. -/
theorem weightedGapSum_eq_sum_words_uncollected {N n : ℕ} (B D : ℂ) (x : Fin (n + 2) → ℤ)
    (p : Fin (n + 2) → ℝ) (σ : Equiv.Perm (Fin (n + 2))) (hx : StrictMono x)
    (hspan : x (Fin.last (n + 1)) - x 0 < (N : ℤ)) (hp : ∀ j, z (p j) ≠ 1) :
    weightedGapSum (N := N) B D x p σ =
      ∑ w : Fin (n + 2) → Bool,
        inclusionWordCoefficient B D p σ w * wordPhase (N := N) x p σ w := by
  rw [weightedGapSum_inclusion_exclusion B D x p σ hx hspan]
  simp_rw [restrictedGapSum_eq_sum_words B D x p σ _ hx hspan hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  unfold inclusionWordCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S _
  ring

end PottsDiscontinuity.BetheAnsatz
