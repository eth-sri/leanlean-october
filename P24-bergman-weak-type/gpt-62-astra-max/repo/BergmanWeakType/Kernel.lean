module

public import BergmanWeakType.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic.Linarith

/-! # Elementary identities for the Bergman kernels

These lemmas establish the kernels' normalizations and the pointwise comparison of the complex
projection with its positive majorant. They do not assert a sharp weak type estimate.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

@[simp]
theorem mem_disk_iff (z : ℂ) : z ∈ disk ↔ ‖z‖ < 1 := by
  simp [disk]

abbrev ClosedDisk := Metric.closedBall (0 : ℂ) 1

theorem kernel_slit {z w : ℂ} (hz : z ∈ disk) (hw : ‖w‖ ≤ 1) : 1-z*star w ∈ Complex.slitPlane := by
  apply Complex.ball_one_subset_slitPlane
  simpa using
    (mul_le_of_le_one_right (norm_nonneg z) hw).trans_lt (by grind [mem_disk_iff])

theorem denominator_ne {z w : ℂ} (hz : z ∈ disk) (hw : ‖w‖ ≤ 1) : 1 - z*star w ≠ 0 :=
  Complex.slitPlane_ne_zero (kernel_slit hz hw)

@[simp] theorem kernel_star (z w : ℂ) : star (kernel z w) = kernel w z := by simp [kernel,mul_comm]

@[simp]
theorem norm_kernel (z w : ℂ) : ‖kernel z w‖ = ‖1 - z * star w‖⁻¹ ^ 2 := by
  simp [kernel]

/-- The weighted pointwise comparison requires no weak type estimate. -/
theorem enorm_weightedProjection_le_weightedPositiveProjection (α : ℝ) (f : ℂ → ℂ)
    (z : ℂ) : ‖weightedProjection α f z‖ₑ ≤ weightedPositiveProjection α f z := by
  simpa [weightedProjection, weightedPositiveProjection] using
    (enorm_integral_le_lintegral_enorm 
      (fun w ↦ weightedKernel α z w * f w))

@[simp]
theorem norm_weightedKernel (α : ℝ) (z w : ℂ) :
    ‖weightedKernel α z w‖ = ‖1 - z * star w‖ ^ (-(α + 2)) := by
  simpa [weightedKernel] using Complex.norm_cpow_real (1 - z * star w) (-(α + 2))

@[simp]
theorem weightedKernel_zero (z w : ℂ) : weightedKernel 0 z w = kernel z w := by
  simp [weightedKernel, kernel, Complex.cpow_neg]

@[simp]
theorem weightedArea_zero : weightedArea 0 = diskArea := by
  simp [weightedArea]

@[simp]
theorem weightedProjection_zero (f : ℂ → ℂ) : weightedProjection 0 f = projection f := by
  funext z
  simp [weightedProjection, projection]

@[simp]
theorem weightedPositiveProjection_zero : weightedPositiveProjection 0 = positiveProjection := by
  funext f z
  simp [weightedPositiveProjection, positiveProjection]

@[simp]
theorem gammaConstant_zero : gammaConstant 0 = 1 := by
  simp [gammaConstant]

open Set in
theorem kernel_continuous (α : ℝ) : ContinuousOn (weightedKernel α).uncurry (disk ×ˢ ClosedDisk) := by
  apply ContinuousOn.cpow_const (by fun_prop)
  intro p hp; apply kernel_slit <;> simp_all

theorem measurableSet_disk : MeasurableSet disk := Metric.isOpen_ball.measurableSet

theorem gammaConstant_pos {α : ℝ} (hα : -1 < α) : 0 < gammaConstant α := by
  apply div_pos
  · exact Real.Gamma_pos_of_pos (by linarith)
  · grind [sq_pos_of_pos, Real.Gamma_pos_of_pos]

end BergmanWeakType
