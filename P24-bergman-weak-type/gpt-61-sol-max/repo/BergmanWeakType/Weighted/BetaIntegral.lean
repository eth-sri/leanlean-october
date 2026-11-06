/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic
import BergmanWeakType.Definitions
import BergmanWeakType.RpowRing
import BergmanWeakType.Derivative

variable {α : ℝ}

/-! # Real beta integrals for the weighted boundary constants -/




open Real

namespace BergmanWeakType

theorem integral_sin_rpow (hα : -1 < α) : ∫ x in 0..π, sin x ^ α = π * gammaConstant α / 2 ^ α :=
  by
  have hraw : ∫ x in 0..π, sin x ^ α = 2 ^ α * Gamma ((α + 1) / 2) ^ 2 / Gamma (α + 1) :=
    by
    have hsub :=
      intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := π) (f := fun x ↦ (1 - cos x) / 2)  (g := fun t ↦ t ^ ((α - 1) / 2) * (1 - t) ^ ((α - 1) / 2)) (by fun_prop)
        (fun x _ ↦ by differentiate)
        (fun x hx ↦ div_nonneg (sin_nonneg_of_nonneg_of_le_pi (by grind [pi_pos]) (by grind [pi_pos])) zero_le_two)
    simp at hsub
    convert_to 2 ^ (-α) * ∫ x in 0..π, sin x ^ α = _ using 1 at hsub
    · rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le pi_pos.le
      intro x hx
      have hs := sin_pos_of_pos_of_lt_pi hx.1 hx.2
      dsimp
      rw [show 1 - (1 - cos x) / 2 = (1 + cos x) / 2 by ring, ←
        Real.mul_rpow (by linarith [cos_le_one x]) (by linarith [neg_one_le_cos x]),
        show (1 - cos x) / 2 * ((1 + cos x) / 2) = sin x ^ 2 / 2 ^ 2 by nlinarith [sin_sq_add_cos_sq x]]
      rpow_ring
    have hb : ∫ x in 0..1, x ^ ((α - 1) / 2) * (1 - x) ^ ((α - 1) / 2) = Gamma ((α + 1) / 2) ^ 2 / Gamma (α + 1) :=
      by
      apply Complex.ofReal_injective
      rw [← intervalIntegral.integral_ofReal]
      calc
        _ = Complex.betaIntegral ((α + 1) / 2 : ℝ) ((α + 1) / 2 : ℝ) :=
          by
          apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
          intro x hx
          simp [Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
          congr 2 <;> ring
        _ = _ := by
          rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by dsimp; linarith) (by dsimp; linarith)]
          rw [← Complex.ofReal_add, add_halves]
          simp only [Complex.Gamma_ofReal]
          push_cast
          ring
    rw [hb] at hsub
    have hn : 0 < (2 : ℝ) ^ α := by positivity
    rw [Real.rpow_neg zero_le_two] at hsub
    grind
  rw [hraw]
  have hG : Gamma ((α + 1) / 2) * Gamma (1 + α / 2) = Gamma (α + 1) * 2 ^ (-α) * sqrt π := by
    convert Gamma_mul_Gamma_add_half_of_pos (show 0 < (α + 1) / 2 by linarith) using 1 <;> congr 2 <;> ring
  rw [Real.rpow_neg zero_le_two] at hG
  have hpos := neg_lt_iff_pos_add.mp hα
  have hhalf : 0 < (2 + α) / 2 := by linarith
  unfold gammaConstant
  field_simp  at hG ⊢
  have hs := congrArg (fun x : ℝ ↦ x ^ 2) hG
  simp [mul_pow, sq_sqrt pi_pos.le] at hs
  nlinarith

end BergmanWeakType
