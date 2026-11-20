/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeComparison
public import CCDN.AuxiliaryPolynomial.HypersurfaceDegreeComparison
public import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.AuxiliaryPolynomial.DegreeBound

/-! Choose one auxiliary degree above both thresholds, then use the appropriate
logarithmic comparison according to the height of the hypersurface. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

abbrev positionedSmallFactor (n : ℕ) (T : ℝ) : ℝ :=
  Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n) T)

abbrev positionedLargeFactor (n : ℕ) (T : ℝ) : ℝ :=
  Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T)

/-- Explicit constant for the positioned absolutely irreducible case. -/
def hypersurfacePositionedAuxiliaryConstant (n : ℕ) (T : ℝ) : ℝ :=
  4 + 8 * (n + 2 : ℝ) + positionedLargeFactor n T + positionedSmallFactor n T

/-- The coefficient-sensitive auxiliary theorem for an equation satisfying the
leading-coefficient positioning inequality. -/
theorem positioned_auxiliary_degree_of_comparison
    {n d t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf0 : f ≠ 0) (hd : 0 < d)
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : CoefficientHeightLE f H)
    (z : Fin t → IntPoint (n + 3)) {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i, InBox (z i) B)
    (bad : Finset ℕ) (hcomp : AuxiliaryRankComparison order f d z bad)
    (hcharge : (∑ p ∈ bad, Real.log p / p) ≤ hypersurfaceHeightChargeBound n d H)
    (T : ℝ) (hT : 0 ≤ T)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| +
      T * d * degreeRoot n d) :
    ∃ M : ℕ,
      (M : ℝ) ≤ hypersurfacePositionedAuxiliaryConstant n T *
        auxDegreeBound n d B (primeSetFactor bad) H ∧
      ∃ g, IsPointAuxiliary f g M z := by
  let L := |((order.leadingCoeff f : ℤ) : ℝ)|
  let Q := auxMainTerm n d B (primeSetFactor bad) H
  let D := auxDegreeScale n d
  let l := auxLogTerm n d B
  let S := positionedSmallFactor n T
  let A := positionedLargeFactor n T
  let C₀ := hypersurfacePositionedAuxiliaryConstant n T
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by positivity
  have hB0 : 0 < B := by linarith
  have hH0 : 0 < H := by linarith
  have hQ : 0 ≤ Q := by dsimp [Q, auxMainTerm]; positivity
  have hl : 0 ≤ l := by dsimp only [l, auxLogTerm]; have := Real.log_nonneg hB; positivity
  have hD : (d : ℝ) ≤ D := le_auxDegreeScale hd
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hS : 0 ≤ S := by dsimp [S]; positivity
  obtain ⟨M, hM, hscale, hthreshold, hbound⟩ :=
    auxiliary_integer_degree_selection (8 * d * (n + 2)) hl
      (add_nonneg (mul_nonneg hS hQ) (mul_nonneg hA (hd0.le.trans hD)))
  refine ⟨M, ?_, ?_⟩
  · push_cast at hbound
    have hC : C₀ = 4 + 8 * (n + 2 : ℝ) + A + S := rfl
    have hn : (0 : ℝ) ≤ n := by positivity
    have hdD := mul_le_mul_of_nonneg_left hD (show 0 ≤ 8 * (n + 2 : ℝ) by positivity)
    change (M : ℝ) ≤ C₀ * (Q + l + D)
    nlinarith only [hbound, hdD, hd1, hD,
      mul_le_mul_of_nonneg_right (show A + 2 + 8 * (n + 2 : ℝ) ≤ C₀ by linarith) (show 0 ≤ D by positivity),
      mul_le_mul_of_nonneg_right (show 1 ≤ C₀ by linarith) hl,
      mul_le_mul_of_nonneg_right (show S ≤ C₀ by linarith) hQ]
  have hMd : d ≤ M := by nlinarith
  by_contra hnone
  have hc := hcomp hB hbox hMd (dvd_of_not_exists_isPointAuxiliary hnone)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hL0 : 0 < L := by linarith
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hn : 0 < n + 1 := Nat.succ_pos _
  apply (not_le_of_gt hthreshold)
  by_cases hsmall : Real.log H ≤ 2 * d * (n + 2 : ℝ) * Real.log B
  · have hheight := (Real.log_le_log hL0 (show L ≤ H from hcoeff (order.degree f))).trans hsmall
    have hscale' := (div_le_iff₀ (show 0 < degreeRoot n d by positivity)).mp hscale
    rw [mul_comm (M : ℝ)] at hscale'
    have hMQ := hypersurface_small_height_degree_bound (A := primeSetFactor bad) hd (show 2 * d ≤ M by nlinarith)
      hB hL hH0 (Real.exp_pos _) hheight hscale' hposition
      (by simpa only [primeSetFactor, Real.log_exp] using hc)
    exact hMQ.trans (le_add_of_nonneg_right (by positivity))
  · have hC := hypersurfaceHeightConstant_one_le (n + 3)
    have := Real.log_nonneg hH
    have hH' : 0 < 1 + Real.log H / (d : ℝ) ^ 2 := by positivity
    dsimp only [hypersurfaceHeightChargeBound] at hcharge
    rw [Real.log_mul (by positivity) hH'.ne'] at hcharge
    have hMbound := hypersurface_large_height_degree_bound hn hd hM
      B L H (hypersurfaceNormalizedError n) T hL hH hT
      (by simpa only [Nat.cast_add, Nat.cast_one, hnR] using le_of_not_ge hsmall)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hposition)
      (by
        unfold NormalizedRankComparison at hc ⊢
        refine le_trans ?_ hc
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simp only [hypersurfaceNormalizedError, Nat.cast_add, Nat.cast_one]
        linarith [mul_le_mul_of_nonneg_left hcharge (show 0 ≤ (n + 1 : ℝ) by positivity)])
    exact (show (M : ℝ) ≤ A * D by simpa only [A, D, positionedLargeFactor, Nat.cast_add, Nat.cast_one] using hMbound).trans
      (le_add_of_nonneg_left (by positivity))
end
end CCDN
