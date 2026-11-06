/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Kernel
import BergmanWeakType.Measure
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

variable {w z : ℂ} {α : ℝ} {f : ℂ → ℂ}

/-! # Integrability of the Bergman integral formulas

For each interior output point, both kernel columns are bounded on the input disk. Consequently
their products with integrable inputs are integrable. The Bochner integrals defining the complex
projections therefore represent genuine integrable functions, and the positive outputs are finite.
-/




open MeasureTheory


namespace BergmanWeakType

theorem measurableSet_disk : MeasurableSet disk := Metric.isOpen_ball.measurableSet

/-- A fixed interior output point keeps the kernel denominator uniformly away from zero. -/
theorem kernel_denominator_norm_lower (z) (hw : w ∈ disk) :
    1 - ‖z‖ ≤ ‖1 - z * star w‖ := by
  have := norm_sub_norm_le (1 : ℂ) (z * star w)
  simp_all
  nlinarith [norm_nonneg z]

theorem norm_weightedKernel_le  (hα : -1 < α)
    (hz : z ∈ disk) (hw : w ∈ disk) :
    ‖weightedKernel α z w‖ ≤ (1 - ‖z‖) ^ (-(α + 2)) := by
  rw [norm_weightedKernel]
  exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr ((mem_disk_iff z).mp hz))
    (kernel_denominator_norm_lower z hw) (by linarith)

@[fun_prop] theorem measurable_weightedKernel (α) : Measurable (weightedKernel α z) := by
  fun_prop [weightedKernel]

/-- Every admissible input gives an integrable weighted kernel integrand at an interior point. -/
theorem integrable_weightedKernel_mul  (hα : -1 < α)
    (hf : Integrable f (weightedArea α))  (hz : z ∈ disk) :
    Integrable (fun w ↦ weightedKernel α z w * f w) (weightedArea α) := by
  apply hf.bdd_mul (measurable_weightedKernel α).aestronglyMeasurable
  exact (ae_mem_disk_weightedArea α).mono fun w hw ↦ norm_weightedKernel_le hα hz hw


theorem kernel_denominator_ne_zero_closed_left {ζ } (hζ : ‖ζ‖ ≤ 1) (hw : w ∈ disk) :
    1 - ζ * star w ≠ 0 := Complex.ne_zero_of_re_pos (kernel_denominator_re_pos (mul_lt_one_of_nonneg_of_lt_one_right
    hζ (norm_nonneg _) ((mem_disk_iff _).mp hw)))


end BergmanWeakType
