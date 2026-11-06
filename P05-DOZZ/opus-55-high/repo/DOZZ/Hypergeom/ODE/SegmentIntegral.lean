/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.DiskPrimitive
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Segment integral formula for the normalized disk primitive. -/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem normalizedDiskPrimitive_sub_center_eq_segmentIntegral
    {c z : ℂ} {r : ℝ} {f : ℂ → E} {y : E}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (hz : z ∈ Metric.ball c r) :
    normalizedDiskPrimitive c r f y hf z - y =
      ∫ t in (0 : ℝ)..1, (z - c) • f (AffineMap.lineMap c z t) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let g : ℝ → ℂ := AffineMap.lineMap c z
  let F : ℝ → E := fun t => normalizedDiskPrimitive c r f y hf (g t)
  let f' : ℝ → E := fun t => (z - c) • f (g t)
  have hr : 0 < r := by
    exact lt_of_le_of_lt (dist_nonneg) (Metric.mem_ball.mp hz)
  have hc : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hseg :=
    (convex_ball c r).mapsTo_lineMap hc hz
  have hderiv : ∀ t ∈ uIcc 0 1, HasDerivAt F (f' t) t := by
    intro t ht
    have ht' : t ∈ Icc 0 1 := by simp_all
    exact (hasDerivAt_normalizedDiskPrimitive hf (hseg ht')).hasFDerivAt.restrictScalars ℝ |>.comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap)
  have hfg : ContinuousOn f' (uIcc 0 1) := by
    have hg : ContinuousOn g (uIcc (0 : ℝ) 1) :=
      AffineMap.lineMap_continuous.continuousOn
    have hfcomp :=
      hf.continuousOn.comp hg fun t ht => hseg (by
        simp_all)
    exact continuousOn_const.smul hfcomp
  have hint : IntervalIntegrable f' volume 0 1 := hfg.intervalIntegrable
  have hF0 : F 0 = y := by
    simp [F, g, normalizedDiskPrimitive_apply_center]
  have hF1 : F 1 = normalizedDiskPrimitive c r f y hf z := by
    simp [F, g]
  calc
    normalizedDiskPrimitive c r f y hf z - y = F 1 - F 0 := by simp_all
    _ = ∫ t in 0..1, f' t := (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm
    _ = ∫ t in 0..1, (z - c) • f _ := rfl

end DOZZ.Proofs
