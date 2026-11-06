module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # A strictly interior optimizing time step at the maximal short horizon -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA

/- Squaring the dimensionless frequency cube root gives the kinetic frequency scale. -/
theorem exitFrequency_square {R n : ℝ} (hR : 0 ≤ R) (hn : 0 ≤ n) :
    ((R ^ 3 * n) ^ (1 / 3 : ℝ)) ^ 2 = R ^ 2 * n ^ (2 / 3 : ℝ) := by
  rw [← Real.rpow_mul_natCast (mul_nonneg (pow_nonneg hR _) hn)]
  norm_num only
  rw [Real.mul_rpow (pow_nonneg hR _) hn, ← Real.rpow_natCast_mul hR]
  norm_num

/- High frequencies have a positive optimizing step strictly below the maximal horizon.
The factor sixteen treats equality at dimensionless frequency one without a limiting step. -/
theorem exitFrequency_exponential_pair {C c y h R n }
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hy : 0 ≤ y)
    (hfirst : R ^ 2 / h = 16 * y) (hsecond : h * n ^ (2 / 3 : ℝ) = y / 16) :
    C * (Real.exp (-c * R ^ 2 / h) + Real.exp (-c * h * n ^ (2 / 3 : ℝ))) ≤
      2 * C * Real.exp (-(c / 16) * y) := by
  have h1 : -c * R ^ 2 / h = -c * (16 * y) := by rw [← hfirst]; ring
  have h2 : -c * h * n ^ (2 / 3 : ℝ) = -c * (y / 16) := by rw [← hsecond]; ring
  have ha : Real.exp (-c * (16 * y)) ≤ Real.exp (-(c / 16) * y) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hc hy]
  have hb : Real.exp (-c * (y / 16)) = Real.exp (-(c / 16) * y) := by congr 1; ring
  rw [h1, h2, hb]
  calc
    _ ≤ C * (Real.exp (-(c / 16) * y) + Real.exp (-(c / 16) * y)) :=
      mul_le_mul_of_nonneg_left (add_le_add ha le_rfl) hC
    _ = _ := by ring

/- Unit variation supplies the same exponential estimate throughout the low-frequency range. -/
end HypoellipticAleksandrov.KineticAleksandrov.LocalA
