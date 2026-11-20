/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Real beta integrals for the weighted boundary constants -/

public section

namespace BergmanWeakType

/-- The substitution `t = (1 - cos θ)/2` sends the whole half-turn to the beta interval. -/
theorem gammaConstant_eq_sineIntegral {α : ℝ} (hα : -1 < α) :
    gammaConstant α = 2 ^ α * (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ α) / Real.pi := by
  let a := (α + 1) / 2
  have ha : 0 < a := by grind +revert
  have h2a : 2 * a = α + 1 := by dsimp [a]; ring
  let u x := (1 - Real.cos x) / 2
  let g (t : ℝ) := (t * (1 - t)) ^ (a - 1)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi) (f := u) (f' := fun x ↦ Real.sin x / 2) (g := g)
    (by unfold u; fun_prop)
    (fun x _ ↦ by simpa [u] using ((Real.hasDerivAt_cos x).const_sub 1).div_const 2)
    (fun x hx ↦ by
      simp only [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hx
      positivity [Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2.le])
  have heq (x : ℝ) (hx : x ∈ Set.Ioo 0 Real.pi) :
      (g ∘ u) x * (Real.sin x / 2) = Real.sin x ^ α / 2 ^ α := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
    have hp : 0 < Real.sin x / 2 := by positivity
    have hm : u x * (1 - u x) = (Real.sin x / 2) ^ 2 := by
      dsimp [u]
      nlinarith [Real.sin_sq_add_cos_sq x]
    dsimp only [Function.comp_apply, g]
    rw [hm, ← Real.rpow_natCast_mul hp.le 2, ← Real.rpow_add_one hp.ne',
      show (↑(2 : ℕ) : ℝ) * (a - 1) + 1 = α by dsimp [a]; ring, Real.div_rpow hs.le (by norm_num)]
  have hbeta : (∫ t in (0 : ℝ)..1, g t) = Real.Gamma a ^ 2 / Real.Gamma (α + 1) := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_div, pow_two, Complex.ofReal_mul, ← Complex.Gamma_ofReal]
    rw [← h2a, two_mul, Complex.ofReal_add, ← Complex.betaIntegral_eq_Gamma_mul_div a a (by simpa using ha) (by simpa using ha)]
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro x hx
    simp [g, Real.mul_rpow hx.1.le (sub_nonneg.mpr hx.2.le), Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
  rw [intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le heq, intervalIntegral.integral_div,
    show u 0 = 0 by simp [u], show u Real.pi = 1 by norm_num [u]] at hsub
  have hp : (2 : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [gammaConstant, (div_eq_iff hp).mp (hsub.trans hbeta)]
  have hG := Real.Gamma_mul_Gamma_add_half_of_pos ha
  rw [show a + 1 / 2 = 1 + α / 2 by linarith, h2a, show 1 - (α + 1) = -α by ring,
    Real.rpow_neg zero_le_two] at hG
  have h := (Real.Gamma_pos_of_pos (show 0 < α + 1 by linarith)).ne'
  have h' := (Real.Gamma_pos_of_pos (show 0 < 1 + α / 2 by linarith)).ne'
  rw [← eq_div_iff h'] at hG
  rw [hG, div_pow, mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
  field_simp [h, h', hp, Real.pi_ne_zero]



end BergmanWeakType
