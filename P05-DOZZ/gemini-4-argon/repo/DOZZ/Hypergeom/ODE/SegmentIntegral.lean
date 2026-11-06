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
    {c z} {r} {f : ℂ → E} {y}
    hf (hz : z ∈ Metric.ball c r) :
    normalizedDiskPrimitive c r f y hf z - y =
      ∫ t in (0 : ℝ)..1, (z - c) • f (AffineMap.lineMap c z t) := by
  let g : ℝ → ℂ := AffineMap.lineMap c z
  let F : ℝ → E := fun t => normalizedDiskPrimitive c r f y hf (g t)
  let f' : ℝ → E := fun t => (z - c) • f (g t)
  have hseg := (convex_ball c r).mapsTo_lineMap (Metric.mem_ball_self (lt_of_le_of_lt (dist_nonneg) (Metric.mem_ball.mp hz))) hz
  have hfg : ContinuousOn f' (uIcc (0 : ℝ) 1) := by
    have hfcomp : ContinuousOn (fun t => f (g t)) (uIcc (0 : ℝ) 1) :=
      hf.continuousOn.comp AffineMap.lineMap_continuous.continuousOn fun t ht => hseg (by
        simpa [uIcc_of_le zero_le_one] using ht)
    change ContinuousOn (fun t => (z - c) • f (g t)) (uIcc (0 : ℝ) 1)
    exact continuousOn_const.smul hfcomp
  calc
    normalizedDiskPrimitive c r f y hf z - y = F 1 - F 0 := by rw [(show F 1 = normalizedDiskPrimitive c r f y hf z by simp [F, g]), (show F 0 = y by simp [F, g, normalizedDiskPrimitive_apply_center])]
    _ = ∫ t in (0 : ℝ)..1, f' t := (intervalIntegral.integral_eq_sub_of_hasDerivAt (by intro t ht; simpa [F, f', g, Function.comp_def, AffineMap.lineMap_apply_module] using ((hasDerivAt_normalizedDiskPrimitive (y := y) hf (hseg (by simpa [uIcc_of_le zero_le_one] using ht))).hasFDerivAt.restrictScalars ℝ |>.comp_hasDerivAt t (AffineMap.hasDerivAt_lineMap (a := c) (b := z)))) hfg.intervalIntegrable).symm
    _ = ∫ t in (0 : ℝ)..1, (z - c) • f (AffineMap.lineMap c z t) := rfl

end DOZZ.Proofs
