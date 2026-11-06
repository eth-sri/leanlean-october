/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.ZeroMass
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Relative kernel perturbation on the retained region -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Powers between zero and two are uniformly Lipschitz on the interval `[1/2,2]`. -/
theorem reflected_rpow_near_one (b t : ℝ) (hb : 0 ≤ b) (hb₂ : b ≤ 2)
    (ht : 1 / 2 ≤ t) (ht₂ : t ≤ 2) : |t ^ b - 1| ≤ 4 * |t - 1| := by
  have hd : ∀ s ∈ Icc (1 / 2 : ℝ) 2,
      HasDerivAt (fun y => y ^ b) (b * s ^ (b - 1)) s := by
    intro s hs
    exact Real.hasDerivAt_rpow_const (Or.inl (by linarith only [hs.1]))
  have hh : ∀ s ∈ Icc (1 / 2 : ℝ) 2, ‖deriv (fun y => y ^ b) s‖ ≤ 4 := by
    intro s hs
    have he : |b - 1| ≤ 1 := abs_le.mpr ⟨by linarith only [hb], by linarith only [hb₂]⟩
    have hpow : s ^ (b - 1) ≤ 2 := by
      have hbound := coulombWeight_rpow_le (L := 2) (by norm_num)
        (by norm_num; exact hs.1) hs.2 (b - 1)
      exact hbound.trans (by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he)
    rw [(hd s hs).deriv, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb,
      abs_of_pos (Real.rpow_pos_of_pos (by linarith only [hs.1]) _)]
    nlinarith only [hb, hb₂, hpow]
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hd s hs).differentiableAt) hh (convex_Icc (1 / 2 : ℝ) 2)
    (show (1 : ℝ) ∈ Icc (1 / 2) 2 by norm_num) (show t ∈ Icc (1 / 2) 2 from ⟨ht, ht₂⟩)
  simpa only [Real.one_rpow, Real.norm_eq_abs] using hm

/-- The perturbed kernel factors through the ratio of its two distances. -/
theorem reflected_kernel_distance_ratio (γ α₁ α₂ α₃ : ℝ) z x (hx : 0 < ‖x‖) :
    gammaHalfKernel γ α₁ α₂ α₃ z x =
      (‖x - z‖ / ‖x‖) ^ (γ ^ 2 / 2) * gammaHalfKernel γ α₁ α₂ α₃ 0 x := by
  unfold gammaHalfKernel
  rw [sub_zero, Real.div_rpow (norm_nonneg _) hx.le]
  field_simp

/-- On a separated retained region, moving the root gives a relative first-order error. -/
theorem reflected_kernel_relative_difference γ α₁ α₂ α₃ (hγ : 0 < γ)
    (hγ₂ : γ < 2) z x (hx : 0 < ‖x‖) (hz : ‖z‖ ≤ ‖x‖ / 2) :
    |gammaHalfKernel γ α₁ α₂ α₃ z x - gammaHalfKernel γ α₁ α₂ α₃ 0 x| ≤
      (4 * (‖z‖ / ‖x‖)) * gammaHalfKernel γ α₁ α₂ α₃ 0 x := by
  let b := γ ^ 2 / 2
  let t := ‖x - z‖ / ‖x‖
  have htd : |t - 1| ≤ ‖z‖ / ‖x‖ := by
    have hn := abs_norm_sub_norm_le (x - z) x
    rw [sub_sub_cancel_left, norm_neg] at hn
    dsimp only [t]
    rw [div_sub_one hx.ne', abs_div, abs_of_pos hx]
    exact div_le_div_of_nonneg_right hn hx.le
  have hK : 0 ≤ gammaHalfKernel γ α₁ α₂ α₃ 0 x := by unfold gammaHalfKernel normPlus; positivity
  rw [reflected_kernel_distance_ratio γ α₁ α₂ α₃ z x hx]
  change |t ^ b * _ - _| ≤ _
  rw [(show t ^ b * gammaHalfKernel γ α₁ α₂ α₃ 0 x - gammaHalfKernel γ α₁ α₂ α₃ 0 x = (t ^ b - 1) * gammaHalfKernel γ α₁ α₂ α₃ 0 x by ring), abs_mul, abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_right
    ((reflected_rpow_near_one b t (by dsimp only [b]; positivity) (by dsimp only [b]; nlinarith only [hγ, hγ₂]) (by apply (le_div_iff₀ hx).mpr; linarith only [(norm_sub_norm_le x z), hz, hx]) (by apply (div_le_iff₀ hx).mpr; linarith only [(norm_sub_le x z), hz, hx])).trans (mul_le_mul_of_nonneg_left htd (by norm_num))) hK

/-- The moving retained kernel stays above one quarter of the zero kernel. -/
theorem reflected_kernel_relative_lower γ α₁ α₂ α₃ (hγ : 0 < γ)
    (hγ₂ : γ < 2) z x (hx : 0 < ‖x‖) (hz : ‖z‖ ≤ ‖x‖ / 2) :
    gammaHalfKernel γ α₁ α₂ α₃ 0 x / 4 ≤ gammaHalfKernel γ α₁ α₂ α₃ z x := by
  have hl : (1 / 4 : ℝ) ≤ (‖x - z‖ / ‖x‖) ^ (γ ^ 2 / 2) := by
    calc
      _ = (1 / 2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ (1 / 2 : ℝ) ^ (γ ^ 2 / 2) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by nlinarith only [hγ, hγ₂])
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) (by apply (le_div_iff₀ hx).mpr; linarith only [(norm_sub_norm_le x z), hz, hx]) (by positivity)
  rw [reflected_kernel_distance_ratio γ α₁ α₂ α₃ z x hx]
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using mul_le_mul_of_nonneg_right hl
    (show 0 ≤ gammaHalfKernel γ α₁ α₂ α₃ 0 x by unfold gammaHalfKernel normPlus; positivity)

end DOZZ.Proofs
