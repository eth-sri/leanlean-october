module
public import Mathlib

@[expose] public section

/-! Conditional quantitative closure of the unequal-scale calculation.
The two analytic estimates are explicit premises. This file does NOT prove
the Poisson truncation, divisor bound, or published affine theorem.
-/
set_option autoImplicit false
noncomputable section
namespace GuthMaynard.Improvement

def unequalScaleBound (R K m n : ℝ) : ℝ :=
  R ^ 2 * K ^ 4 * m ^ 2 + R * K ^ 3 * n ^ 2

/-- Final scale absorption, keeping the prefactor RK before the smaller
affine square average Q. E and H carry the two uniform losses. -/
theorem unequal_reduction_of_estimates {J Q E H R K m n : ℝ}
    (hE : 0 ≤ E) (hH : 1 ≤ H) (hK : 0 ≤ K) (hKR : K ≤ R)
    (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hpoisson : J ≤ E * (R ^ 2 * K ^ 4 * m ^ 2 + R * K * n * Real.sqrt Q))
    (haffine : Q ≤ H * (K ^ 6 * m ^ 2 + K ^ 4 * n ^ 2)) :
    J ≤ 2 * E * Real.sqrt H * unequalScaleBound R K m n := by
  have hR : 0 ≤ R := hK.trans hKR
  have hH0 : 0 ≤ H := by linarith
  have hcross : R * K ^ 4 * m * n ≤ R ^ 2 * K ^ 4 * m ^ 2 + R * K ^ 3 * n ^ 2 := by
    have h1 : 0 ≤ K ^ 4 * (R * m - n) ^ 2 := by positivity
    have h2 : 0 ≤ K ^ 4 * (R * m) ^ 2 := by positivity
    have h3 : 0 ≤ (R - K) * K ^ 3 * n ^ 2 := by positivity
    nlinarith
  have hroot : Real.sqrt Q ≤ Real.sqrt H * (K ^ 3 * m + K ^ 2 * n) := by
    have hsq : K ^ 6 * m ^ 2 + K ^ 4 * n ^ 2 ≤ (K ^ 3 * m + K ^ 2 * n) ^ 2 := by
      have : 0 ≤ K ^ 5 * m * n := by positivity
      nlinarith
    calc
      Real.sqrt Q ≤ Real.sqrt (H * (K ^ 3 * m + K ^ 2 * n) ^ 2) :=
        Real.sqrt_le_sqrt (haffine.trans (mul_le_mul_of_nonneg_left hsq hH0))
      _ = Real.sqrt H * (K ^ 3 * m + K ^ 2 * n) := by
        rw [Real.sqrt_mul hH0, Real.sqrt_sq (by positivity)]
  have hroot1 : 1 ≤ Real.sqrt H := Real.one_le_sqrt.mpr hH
  have hlow : R ^ 2 * K ^ 4 * m ^ 2 ≤
      Real.sqrt H * (R ^ 2 * K ^ 4 * m ^ 2) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hroot1
      (show 0 ≤ R ^ 2 * K ^ 4 * m ^ 2 by positivity)
  have hhigh : R * K * n * Real.sqrt Q ≤
      Real.sqrt H * (R * K ^ 4 * m * n + R * K ^ 3 * n ^ 2) := by
    convert mul_le_mul_of_nonneg_left hroot (show 0 ≤ R * K * n by positivity) using 1
    ring
  have habsorb := mul_le_mul_of_nonneg_left hcross (Real.sqrt_nonneg H)
  apply hpoisson.trans
  have hsum : R ^ 2 * K ^ 4 * m ^ 2 + R * K * n * Real.sqrt Q ≤
      2 * Real.sqrt H * unequalScaleBound R K m n := by
    dsimp [unequalScaleBound]
    nlinarith
  convert mul_le_mul_of_nonneg_left hsum hE using 1
  ring

end GuthMaynard.Improvement
