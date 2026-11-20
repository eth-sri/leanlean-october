/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import BergmanWeakType.Weighted.BetaIntegral
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! # The circular boundary-kernel normalizer

The normalizer is the average of the actual positive boundary kernel. Its sharp
estimate uses the radial equation and a beta integral at the boundary.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace BergmanWeakType

/-- Circular mean of the positive boundary kernel at radial coordinate `r`. -/
def normalizer (α r : ℝ) : ℝ :=
  Real.circleAverage (fun z : ℂ ↦ ‖1 - z‖ ^ (-(α + 2))) 0 r

@[simp] theorem normalizer_zero (α : ℝ) : normalizer α 0 = 1 := by
  simp [normalizer]

theorem normalizer_nonneg (α r : ℝ) : 0 ≤ normalizer α r :=
  Real.circleAverage_nonneg_of_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

theorem circleAverage_boundary_power {α : ℝ} (hα : -1 < α) :
    Real.circleAverage (fun ζ : ℂ ↦ ‖1 - ζ‖ ^ α) 0 1 = gammaConstant α := by
  rw [Real.circleAverage_def]
  rw [intervalIntegral.integral_congr_Ioo_of_le Real.two_pi_pos.le
    (g := fun θ ↦ 2 ^ α * Real.sin (θ / 2) ^ α) ?_, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun θ ↦ Real.sin θ ^ α) (by norm_num)]
  · simp only [zero_div, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
    rw [gammaConstant_eq_sineIntegral hα]
    ring
  intro θ hθ
  have hs : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul]
  rw [norm_sub_rev, mul_comm (θ : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.mul_rpow (by norm_num) hs]

theorem circleAverage_weightedKernel_norm (α : ℝ) (z : ℂ) (r : ℝ) :
    Real.circleAverage (fun w ↦ ‖weightedKernel α z w‖) 0 r = normalizer α (r * ‖z‖) := by
  unfold normalizer
  conv_lhs => rw [Real.circleAverage_def]
  rw [Real.circleAverage_eq_integral_add (Complex.arg (star z))]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [norm_weightedKernel, ← norm_star (1 - z * star (circleMap 0 r θ))]
  simp only [star_sub, star_one, star_mul, star_star]
  nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I (star z)]
  simp only [circleMap, zero_add, norm_star, Complex.ofReal_mul, Complex.ofReal_add, add_mul,
    Complex.exp_add]
  congr 3; ring

end BergmanWeakType
