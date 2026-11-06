/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Hypergeom.Planar.RadialCriteria
import Mathlib.MeasureTheory.Group.Measure

/-! Positive planar kernels controlling the two near-diagonal fusion sectors. -/

open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Translation preserves the radial positive integral on a disk. -/
theorem translated_ball_rpow_integral (u : ℂ) (R b : ℝ) :
    (∫⁻ v in Metric.ball u R, ENNReal.ofReal (‖u - v‖ ^ b)) =
      ∫⁻ v in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖v‖ ^ b) := by
  let f : ℂ → ℝ≥0∞ := (Metric.ball u R).indicator (fun v => ENNReal.ofReal (‖u - v‖ ^ b))
  have hf : Measurable f := (ENNReal.measurable_ofReal.comp
    ((measurable_const.sub measurable_id).norm.pow_const b)).indicator measurableSet_ball
  have hcomp : (fun x : ℂ => f (x + u)) =
      (Metric.ball (0 : ℂ) R).indicator (fun x => ENNReal.ofReal (‖x‖ ^ b)) := by
    funext x
    have hsub : u - (x + u) = -x := by abel
    have hmem : x + u ∈ Metric.ball u R ↔ x ∈ Metric.ball (0 : ℂ) R := by
      simp [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]
    by_cases hx : x ∈ Metric.ball (0 : ℂ) R
    · simp [f, Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx, hsub, norm_neg]
    · simp [f, Set.indicator_of_notMem (hmem.not.mpr hx), Set.indicator_of_notMem hx]
  have h := (measurePreserving_add_right volume u).lintegral_comp hf
  rw [show (fun x : ℂ => f (x + u)) = _ from hcomp] at h
  dsimp [f] at h
  rw [lintegral_indicator measurableSet_ball, lintegral_indicator measurableSet_ball] at h
  exact h.symm

end DOZZ.Proofs
