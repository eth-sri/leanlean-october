/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Weighted.NormalizerEndpoint
import Mathlib.Tactic

/-! # Angular means of weighted kernel columns -/






namespace BergmanWeakType

theorem circleAverage_weightedKernel_norm (α) (z) {r} (hr : 0 ≤ r) :
    Real.circleAverage (fun w ↦ ‖weightedKernel α z w‖) 0 r = normalizer α (r * ‖z‖) :=
  by
  rw [Real.circleAverage_eq_circleAverage_zero_one]
  simp
  simp_rw [← mul_assoc, ← Complex.star_def]
  trans Real.circleAverage (fun ξ : ℂ ↦ ‖1 - z * r * ξ‖ ^ (-(α + 2))) 0 1
  · rw [← Real.circleAverage_zero_one_congr_inv]
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    have hζ' : ‖ζ‖ = 1 := by simp_all
    dsimp only
    rw [Complex.inv_def, ← Complex.sq_norm, hζ']
    simp
  · have ha : ‖z * (r : ℂ)‖ = r * ‖z‖ := by simp [abs_of_nonneg hr, mul_comm]
    unfold normalizer boundaryMoment
    rw [Real.circleAverage_eq_circleAverage_zero_one]
    rw [← ha, Real.circleAverage_def,
      Real.circleAverage_eq_integral_add
         (Complex.arg (z * r))]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I (z * r)]
    simp [circleMap, add_mul, Complex.exp_add]
    ring

end BergmanWeakType
