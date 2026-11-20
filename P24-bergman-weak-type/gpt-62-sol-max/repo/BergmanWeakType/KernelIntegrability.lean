/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Kernel
public import BergmanWeakType.Measure
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Integrability of the Bergman integral formulas

For each interior output point, both kernel columns are bounded on the input disk. Consequently
their products with integrable inputs are integrable. The Bochner integrals defining the complex
projections therefore represent genuine integrable functions, and the positive outputs are finite.
-/

public section

open MeasureTheory Metric

namespace BergmanWeakType

theorem measurableSet_disk : MeasurableSet disk := Metric.isOpen_ball.measurableSet

theorem continuousOn_weightedKernel_prod (α : ℝ) :
    ContinuousOn (fun p : ℂ × ℂ ↦ weightedKernel α p.1 p.2)
      {p | ‖p.1‖ * ‖p.2‖ < 1} := by
  apply ContinuousOn.cpow_const (by fun_prop)
  intro p hp
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (kernel_denominator_re_pos hp))

theorem memLp_weightedKernel_top {α : ℝ} {z : ℂ} (hz : z ∈ disk) :
    MemLp (weightedKernel α z) ⊤ (weightedArea α) := by
  have hc : ContinuousOn (weightedKernel α z) (closedBall 0 1) :=
    (continuousOn_weightedKernel_prod α).comp (f := fun w : ℂ ↦ (z, w)) (by fun_prop)
      (fun _ hw ↦ mul_norm_lt_one hz (by simpa using hw))
  obtain ⟨M, hM⟩ := (isCompact_closedBall _ _).exists_bound_of_continuousOn hc
  have ha := ae_mem_disk_weightedArea α
  refine memLp_top_of_bound ?_ M (ha.mono fun w hw ↦ hM w (ball_subset_closedBall hw))
  rw [← Measure.restrict_eq_self_of_ae_mem ha]
  exact (hc.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_disk

end BergmanWeakType
