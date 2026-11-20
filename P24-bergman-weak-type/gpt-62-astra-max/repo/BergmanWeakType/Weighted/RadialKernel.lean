/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.Normalizer

/-! # Angular means of weighted kernel columns -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace BergmanWeakType

theorem circleAverage_mul_eq_norm (f : ℂ → ℝ) (a : ℂ) (r : ℝ) :
    Real.circleAverage (fun ζ ↦ f (a * ζ)) 0 r = Real.circleAverage f 0 (r*‖a‖) := by
  rw [Real.circleAverage_def,
    Real.circleAverage_eq_integral_add  (Complex.arg a)]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  congr 1
  nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I a]
  simp only [circleMap, Complex.ofReal_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

theorem circleAverage_weightedKernel_norm (α : ℝ) (z : ℂ) (r : ℝ) :
    Real.circleAverage (fun w ↦ ‖weightedKernel α z w‖) 0 r = normalizer α (r * ‖z‖) := by
  have h (w : ℂ) : ‖1 - z*star w‖ = ‖1-star z*w‖ := by
    rw [← norm_star (1-z*star w)]; simp
  simpa only [norm_weightedKernel, h, radialMoment, norm_star] using
    circleAverage_mul_eq_norm (fun u ↦ ‖1-u‖^(-(α+2))) (star z) r

end BergmanWeakType
