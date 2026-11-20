/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Measure
public import BergmanWeakType.Weighted.BetaIntegral
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Complex.Harmonic.Poisson

/-! # The circular boundary-kernel normalizer

The normalizer is the average of the actual positive boundary kernel. Its sharp
bound requires a circle change of variables and a beta integral; neither estimate
is included as a hypothesis or an axiom here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

def radialMoment (p : ℝ) := Real.circleAverage (fun z : ℂ ↦ ‖1-z‖^p) 0

/-- Circular mean of the positive boundary kernel at radial coordinate `r`. -/
abbrev normalizer (α : ℝ) := radialMoment (-(α+2))

@[simp] theorem normalizer_zero (α : ℝ) : normalizer α 0 = 1 := by simp [radialMoment]

theorem normalizer_nonneg (α r : ℝ) : 0 ≤ normalizer α r :=
  Real.circleAverage_nonneg_of_nonneg (by bound)

theorem chord_length {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    ‖1 - circleMap 0 1 θ‖ = 2 * Real.sin (θ / 2) := by
  have h := Real.sin_pos_of_pos_of_lt_pi (by grind : 0 < θ/2) (by grind)
  rw [circleMap, zero_add, Complex.ofReal_one, one_mul, norm_sub_rev,
    mul_comm (θ : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem circleAverage_boundary_power {α : ℝ} (hα : -1 < α) :
    radialMoment α 1 = gammaConstant α := by
  rw [radialMoment, Real.circleAverage_def]
  have heq : (∫ θ in 0..2 * Real.pi, ‖1 - circleMap 0 1 θ‖ ^ α) =
      2 ^ α * (∫ θ in 0..2 * Real.pi, Real.sin (θ / 2) ^ α) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
    intro θ hθ
    dsimp only
    rw [chord_length hθ, Real.mul_rpow (by norm_num) (Real.sin_nonneg_of_nonneg_of_le_pi (by grind) (by grind))]
  rw [heq, intervalIntegral.integral_comp_div (fun θ ↦ Real.sin θ ^ α) (two_ne_zero)]
  simp
  have := scaled_integral_sin hα
  grind [Real.pi_pos]

end BergmanWeakType
