module

public import BergmanWeakType.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
  simp [disk, Metric.mem_ball, dist_zero_right]

theorem kernel_denominator_ne_zero_closed_input {R : ℝ} (hR : R < 1) {z w : ℂ}
    (hz : z ∈ Metric.closedBall 0 R) (hw : w ∈ Metric.closedBall 0 1) :
    1 - z * star w ≠ 0 := by
  have hz' : ‖z‖ < 1 := (by simpa using hz : ‖z‖ ≤ R).trans_lt hR
  have hw' : ‖w‖ ≤ 1 := by simpa using hw
  have hm : ‖z * star w‖ < 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_right (norm_nonneg _) hw').trans_lt hz'
  intro heq
  have h2 : ‖z * star w‖ = 1 := by rw [← sub_eq_zero.mp heq, norm_one]
  linarith

theorem kernel_denominator_ne_zero {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    1 - z * star w ≠ 0 := by
  have hz1 : ‖z‖ < 1 := (mem_disk_iff z).mp hz
  have hw1 : ‖w‖ < 1 := (mem_disk_iff w).mp hw
  refine kernel_denominator_ne_zero_closed_input (R := (‖z‖ + 1) / 2) ?_ ?_ ?_
  · linarith
  · simp only [Metric.mem_closedBall, dist_zero_right]; linarith
  · simp only [Metric.mem_closedBall, dist_zero_right]; linarith

/-- The kernel's base lies in the right half-plane on the disk. -/
theorem kernel_denominator_re_pos {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    0 < (1 - z * star w).re := by
  have hmul : ‖z * star w‖ < 1 := by
    rw [norm_mul, norm_star]
    nlinarith [(mem_disk_iff z).mp hz, (mem_disk_iff w).mp hw, norm_nonneg z, norm_nonneg w]
  have h1 := Complex.re_le_norm (1 - z * star w)
  have h2 := Complex.re_le_norm (z * star w)
  rw [Complex.sub_re, Complex.one_re] at h1
  rw [Complex.sub_re, Complex.one_re]
  linarith

@[simp]
theorem norm_kernel (z w : ℂ) : ‖kernel z w‖ = ‖1 - z * star w‖⁻¹ ^ 2 := by
  simp [kernel, norm_pow, norm_inv]

/-- The positive extended integral bounds the complex Bochner integral pointwise. -/
theorem enorm_projection_le_positiveProjection (f : ℂ → ℂ) (z : ℂ) :
    ‖projection f z‖ₑ ≤ positiveProjection f z := by
  simpa [projection, positiveProjection, enorm_mul, ← ofReal_norm] using
    (enorm_integral_le_lintegral_enorm (μ := diskArea) (fun w ↦ kernel z w * f w))

/-- The weighted pointwise comparison requires no weak type estimate. -/
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
theorem weightedPositiveProjection_zero (f : ℂ → ℂ) :
    weightedPositiveProjection 0 f = positiveProjection f := by
  funext z
  simp [weightedPositiveProjection, positiveProjection]

theorem gammaConstant_pos {α : ℝ} (hα : -1 < α) : 0 < gammaConstant α :=
  div_pos (Real.Gamma_pos_of_pos (by linarith))
    (sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)))

end BergmanWeakType
