/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Weighted.RadialKernel
import BergmanWeakType.Weighted.PolarPotential
import Mathlib.Tactic



/-! # The circular normalizer as a polar kernel potential -/



noncomputable section

open MeasureTheory Real

namespace BergmanWeakType.Weighted

abbrev boundaryIntegral (H : PolarFamily) :=
  polarIntegral H (circleMap 0 1) (volume.restrict (Set.Icc 0 (2 * π))) (fun _ ↦ (2 * π)⁻¹)

def integrable_boundaryDensity :=
  integrable_const (μ := volume.restrict (Set.Icc 0 (2 * π))) (2 * π)⁻¹

theorem polarIntegral_boundary_eq_normalizer (α r θ : ℝ) :
    boundaryIntegral (polarKernel (-(α + 2) / 2)) r θ = normalizer α r :=
  by
  have hcircle := circleAverage_weightedKernel_norm α (circleMap 0 r θ)  zero_le_one
  simp [normalizer, boundaryMoment, circleAverage_abs_radius] at hcircle
  rw [boundaryIntegral, polarIntegral]
  simp_rw [polarKernel_eq_norm_weightedKernel]
  rw [integral_mul_const, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simpa [normalizer, boundaryMoment, Real.circleAverage_def, mul_comm] using hcircle


end BergmanWeakType.Weighted
