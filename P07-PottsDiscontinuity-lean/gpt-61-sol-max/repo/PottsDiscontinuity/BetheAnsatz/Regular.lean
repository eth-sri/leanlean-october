module
public import Mathlib

public import PottsDiscontinuity.Bethe.RatioProducts
public import PottsDiscontinuity.BetheAnsatz.GapTransfer
public import PottsDiscontinuity.BetheAnsatz.NonconstantWords

/-!
# The non-degenerate coordinate Bethe Ansatz

The full transfer action is the finite gap sum. Its word encoding and pairwise
cancellation leave the two constant words, giving the regular eigenvalue.
-/

@[expose] public section

open Finset Complex Matrix Classical

namespace PottsDiscontinuity.BetheAnsatz

section

variable {n : ℕ} (c : ℝ) (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
include c p σ

/-- The all-M coefficient is independent of the permutation. -/
theorem wordCoefficient_false  :
    wordCoefficient c p σ (fun _ => false) = ∏ j, M c (z (p j)) := by
  simpa only [wordCoefficient, Bool.false_eq_true, ↓reduceIte] using
    Equiv.prod_comp σ  fun j => M c (z (p j)) 

/-- The all-L coefficient is independent of the permutation. -/
theorem wordCoefficient_true  :
    wordCoefficient c p σ (fun _ => true) = ∏ j, L c (z (p j)) := by
  simpa only [wordCoefficient, ↓reduceIte, Equiv.Perm.mul_apply] using
    Equiv.prod_comp (σ * finRotate (n + 1))  fun j => L c (z (p j)) 

end

section

variable {N n : ℕ} (x : Fin (n + 1) → ℤ) (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
include N x p σ

/-- The all-M phase is the ordinary plane wave. -/
theorem wordPhase_false  :
    wordPhase (N := N) x p σ (fun _ => false) = planeWave p σ x := rfl

/-- The all-L phase is the plane wave at the lifted predecessor coordinates. -/
theorem wordPhase_true  :
    wordPhase (N := N) x p σ (fun _ => true) =
      planeWave p σ (cyclicPredecessorPositions N x) := rfl

end

section

variable {N n : ℕ}
include N n

/-- Contribution of the constant M word. -/
theorem sum_wordTerm_false  (c : ℝ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) :
     ∑ σ, wordTerm (N := N) c x p σ (fun _ => false)  =
      (∏ j, M c (z (p j))) * coordinateWave (anisotropy c) p x := by
  simp only [wordTerm, wordCoefficient_false, wordPhase_false, coordinateWave, Finset.mul_sum]
  grind

section

variable {c : ℝ} (hc : 2 < c)
include hc

/-- Contribution of the constant L word, using the toroidal Bethe relation. -/
theorem sum_wordTerm_true   (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (hBE : BetheEquations N (anisotropy c) p) :
     ∑ σ, wordTerm (N := N) c x p σ (fun _ => true)  =
      (∏ j, L c (z (p j))) * coordinateWave (anisotropy c) p x := by
  rw [coordinateWave_cyclicPredecessor (anisotropy_lt_neg_one hc) p hBE x]
  simp only [wordTerm, wordCoefficient_true, wordPhase_true, coordinateWave, Finset.mul_sum]
  grind

/-- The regular eigenvalue identity for the finite cyclic gap expression, n≥2. -/
theorem sum_amplitude_cyclicGapSum_regular  
    (x : Fin (n + 2) → ℤ) (hx : StrictMono x)
    (hspan : x (Fin.last (n + 1)) - x 0 < (N : ℤ))
    (p : Fin (n + 2) → ℝ) (hp : ∀ j, z (p j) ≠ 1)
    (hBE : BetheEquations N (anisotropy c) p) :
     ∑ σ, amplitude (anisotropy c) p σ * cyclicGapSum c N x p σ  =
      eigenvalueRegular c p * coordinateWave (anisotropy c) p x := by
  simp_rw [cyclicGapSum_eq_sum_words c x p _ hx hspan hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc]
  change  ∑ w, ∑ σ, wordTerm (N := N) c x p σ w  = _
  rw [sum_wordTerms_eq_constant_words hc x p hp hBE, sum_wordTerm_true hc x p hBE,
    sum_wordTerm_false, eigenvalueRegular, add_mul]

/-- Theorem 3.1, non-degenerate branch for n≥2, on the actual full complex matrix.
Distinctness and the half-filling bound are not needed for this identity. -/
theorem betheAnsatz_regular  
    (p : Fin (n + 2) → ℝ) (hp : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
    (hp0 : ∀ j, p j ≠ 0) (hBE : BetheEquations N (anisotropy c) p) :
    (SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ betheVector (anisotropy c) p =
      eigenvalueRegular c p • betheVector (anisotropy c) p := by
  funext x
  by_cases hx : x.card = n + 2
  · let s : SixVertex.State N (n + 2) := ⟨x, hx⟩
    have ht := transfer_betheVector_eq_cyclicGapSum c (anisotropy_lt_neg_one hc) p hBE s
    rw [sum_amplitude_cyclicGapSum_regular hc (positions s) (positions_strictMono s)
      (positions_span_lt s) p (fun j => z_ne_one (hp j) (hp0 j)) hBE] at ht
    change ((SixVertex.transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ
      extendByZero (blockWave (anisotropy c) p)) s.1 =
      eigenvalueRegular c p * extendByZero (blockWave (anisotropy c) p) s.1
    rw [extendByZero_coe]
    exact ht
  · rw [complex_transfer_mulVec_supported c (n + 2) (betheVector (anisotropy c) p)
      (fun y hy => betheVector_eq_zero _ _ hy) x hx]
    simp only [Pi.smul_apply, smul_eq_mul, betheVector_eq_zero _ _ hx, mul_zero]

end

end

end PottsDiscontinuity.BetheAnsatz
