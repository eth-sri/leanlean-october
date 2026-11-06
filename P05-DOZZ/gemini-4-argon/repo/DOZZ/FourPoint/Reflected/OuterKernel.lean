/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfKernel
import Mathlib.Tactic

/-! # Deterministic outer-kernel domination and the reflected limiting density -/

public section

namespace DOZZ.Proofs

/-- On the retained outer region the perturbed kernel is dominated by its zero kernel. -/
theorem reflected_outer_kernel_bound (γ α₁ α₂ α₃ : ℝ) z x
    (hsep : ‖z‖ ≤ ‖x‖) :
    gammaHalfKernel γ α₁ α₂ α₃ z x ≤
      (2 : ℝ) ^ (γ ^ 2 / 2) * gammaHalfKernel γ α₁ α₂ α₃ 0 x := by
  have hk : 0 ≤ γ ^ 2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
  have hdist : ‖x - z‖ ≤ 2 * ‖x‖ :=
    (norm_sub_le x z).trans (by linarith only [hsep])
  have hpow := Real.rpow_le_rpow (norm_nonneg (x - z)) hdist hk
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg x)] at hpow
  have hn : 0 ≤ normPlus x ^ (γ * (α₁ + α₂ + α₃ - γ / 2)) :=
    Real.rpow_nonneg (by unfold normPlus; positivity) _
  unfold gammaHalfKernel
  rw [sub_zero]
  calc
    _ ≤ ((2 : ℝ) ^ (γ ^ 2 / 2) * ‖x‖ ^ (γ ^ 2 / 2) *
        normPlus x ^ (γ * (α₁ + α₂ + α₃ - γ / 2))) /
        (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hn) (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))
    _ = _ := by ring

/-- At zero the half-charge kernel has exactly the effective first charge `α₁-γ/2`. -/
theorem reflected_zero_kernel_weight (γ α₁ α₂ α₃ : ℝ) x
    (hx : x ≠ 0) (hx1 : x ≠ 1) :
    gammaHalfKernel γ α₁ α₂ α₃ 0 x =
      normPlus x ^ (γ * ((α₁ - γ / 2) + α₂ + α₃)) /
        (‖x‖ ^ (γ * (α₁ - γ / 2)) * ‖x - 1‖ ^ (γ * α₂)) := by
  have hxpos := norm_pos_iff.mpr hx
  have hprod := Real.rpow_add hxpos (γ ^ 2 / 2) (γ * (α₁ - γ / 2))
  rw [(show γ ^ 2 / 2 + γ * (α₁ - γ / 2) = γ * α₁ by ring)] at hprod
  unfold gammaHalfKernel
  rw [sub_zero, hprod,
    show α₁ + α₂ + α₃ - γ / 2 = (α₁ - γ / 2) + α₂ + α₃ by ring]
  field_simp

/-- The kernel is continuous in the moving insertion for every fixed integration point. -/
theorem reflected_outer_kernel_continuous γ α₁ α₂ α₃ x :
    Continuous (fun z : ℂ => gammaHalfKernel γ α₁ α₂ α₃ z x) := by
  exact (((Real.continuous_rpow_const (div_nonneg (sq_nonneg γ) (by norm_num : (0 : ℝ) ≤ 2))).comp (((continuous_const : Continuous (fun _ => x)).sub continuous_id).norm)).mul_const _).div_const _

end DOZZ.Proofs
