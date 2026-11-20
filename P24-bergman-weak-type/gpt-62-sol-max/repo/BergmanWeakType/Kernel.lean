module

public import BergmanWeakType.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

/-! # Elementary identities for the Bergman kernels

These lemmas establish the kernels' normalizations and the pointwise comparison of the complex
projection with its positive majorant. They do not assert a sharp weak type estimate.
-/

public section

open MeasureTheory

namespace BergmanWeakType

@[simp]
theorem mem_disk_iff (z : ℂ) : z ∈ disk ↔ ‖z‖ < 1 := by
  simp [disk]

theorem mul_norm_lt_one {z w : ℂ} (hz : z ∈ disk) (hw : ‖w‖ ≤ 1) : ‖z‖ * ‖w‖ < 1 :=
  (mul_le_of_le_one_right (norm_nonneg z) hw).trans_lt ((mem_disk_iff _).mp hz)

theorem kernel_denominator_re_pos {z w : ℂ} (h : ‖z‖ * ‖w‖ < 1) :
    0 < (1 - z * star w).re := by
  rw [Complex.sub_re, Complex.one_re]
  apply sub_pos.mpr ((Complex.re_le_norm _).trans_lt ?_)
  simp_all

theorem kernel_denominator_ne_zero {z w : ℂ} (hz : z ∈ disk) (hw : ‖w‖ ≤ 1) :
    1 - z * star w ≠ 0 :=
  fun he ↦ by simpa only [he, Complex.zero_re, lt_irrefl] using kernel_denominator_re_pos (mul_norm_lt_one hz hw)

theorem enorm_weightedProjection_le_weightedPositiveProjection (α : ℝ) (f : ℂ → ℂ)
    (z : ℂ) : ‖weightedProjection α f z‖ₑ ≤ weightedPositiveProjection α f z := by
  simpa [weightedProjection, weightedPositiveProjection, enorm_mul, ← ofReal_norm] using
    (enorm_integral_le_lintegral_enorm (μ := weightedArea α)
      (fun w ↦ weightedKernel α z w * f w))

@[simp]
theorem norm_weightedKernel (α : ℝ) (z w : ℂ) :
    ‖weightedKernel α z w‖ = ‖1 - z * star w‖ ^ (-(α + 2)) := by
  simpa [weightedKernel] using Complex.norm_cpow_real (1 - z * star w) (-(α + 2))

@[simp]
theorem weightedKernel_zero (z w : ℂ) : weightedKernel 0 z w = kernel z w := by
  simp [weightedKernel, kernel, Complex.cpow_neg, ← inv_pow]

@[simp]
theorem weightedArea_zero : weightedArea 0 = diskArea := by
  simp [weightedArea]

@[simp]
theorem weightedProjection_zero (f : ℂ → ℂ) : weightedProjection 0 f = projection f := by
  funext z
  simp [weightedProjection, projection]

@[simp]
theorem weightedPositiveProjection_zero :
    weightedPositiveProjection 0 = positiveProjection := by
  funext f z
  simp [weightedPositiveProjection, positiveProjection]

@[simp]
theorem gammaConstant_zero : gammaConstant 0 = 1 := by
  simp [gammaConstant]

theorem gammaConstant_pos {α : ℝ} (hα : -1 < α) : 0 < gammaConstant α := by
  exact div_pos (Real.Gamma_pos_of_pos (by linarith)) (sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)))

end BergmanWeakType
