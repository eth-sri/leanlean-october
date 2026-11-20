/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.RootedFreezing
public import DOZZ.FourPoint.TaylorOneRootIdentity
public import DOZZ.FourPoint.TaylorRadialBall
import Mathlib.Tactic

/-! # The deleted-disk error at the reflected freezing power -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Near zero the unperturbed kernel has radial power `κ-2`. -/
theorem reflected_zero_kernel_local_upper (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ)
    (x : ℂ) (hx : ‖x‖ < 1 / 2) :
    gammaHalfKernel γ α₁ α₂ α₃ 0 x ≤
      (2 : ℝ) ^ |γ * α₂| * ‖x‖ ^ (γ * (Q γ - α₁) - 2) := by
  by_cases hx0 : x = 0
  · subst x
    have hk : γ ^ 2 / 2 ≠ 0 := (div_pos (sq_pos_of_pos hγ) (by norm_num)).ne'
    simp only [gammaHalfKernel, sub_zero, norm_zero, Real.zero_rpow hk, zero_mul, zero_div]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hx1 : x ≠ 1 := by rintro rfl; norm_num at hx
  have he : -(γ * (α₁ - γ / 2)) = γ * (Q γ - α₁) - 2 := by
    unfold Q
    field_simp
    ring
  rw [reflected_zero_kernel_weight γ α₁ α₂ α₃ x hx0 hx1]
  unfold normPlus
  rw [max_eq_left (by linarith only [hx] : ‖x‖ ≤ 1), Real.one_rpow,
    div_eq_mul_inv, one_mul, mul_inv, ← Real.rpow_neg hn.le,
    ← Real.rpow_neg (norm_nonneg (x - 1)), he]
  simpa only [abs_neg, mul_comm] using
    mul_le_mul_of_nonneg_left (norm_sub_one_rpow_le_of_norm_lt_half hx (-(γ * α₂)))
      (Real.rpow_nonneg hn.le (γ * (Q γ - α₁) - 2))

/-- Rooting and the local freezing estimate give the full deleted-disk power `κ+δ`. -/
theorem reflected_deleted_disk_weight_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα₁ : α₁ < Q γ)
    (hreflect : Q γ - α₁ < γ / 2) (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ r : ℝ, 0 < r → r < ε₀ →
      (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) r,
          ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂M ω) *
        (reflectedRetainedZeroMass γ α₁ α₂ α₃ r (M ω)) ^
          (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1)) ∂P) ≤
      ENNReal.ofReal (C * r ^
        (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2)) := by
  let q : ℝ := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1
  let κ : ℝ := γ * (Q γ - α₁)
  let δ : ℝ := (α₁ + γ / 2 - Q γ) ^ 2 / 2
  let w : ℝ := (2 : ℝ) ^ |γ * α₂|
  have hκ : 0 < κ := mul_pos hγ (sub_pos.mpr hα₁)
  have hw : 0 < w := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨Cr, εr, hCr, hεr, hb⟩ := reflected_retainedZero_rooted_inverse_freezing
    P X M γ α₁ α₂ α₃ hγ hγ₂ hα₁ hreflect hs hX hM
  obtain ⟨Cd, hCd, hd⟩ := small_ball_kernel_bound (gammaHalfKernel γ α₁ α₂ α₃ 0) (κ - 2) w
    (by linarith) hw (reflected_zero_kernel_local_upper γ α₁ α₂ α₃ hγ)
  refine ⟨Cr * Cd, min εr (1 / 2), mul_pos hCr hCd, lt_min hεr (by norm_num), ?_⟩
  intro r hr hr₀
  obtain ⟨hrr, hrh⟩ := lt_min_iff.mp hr₀
  have hG := (retainedZeroMass_measurable γ (-γ / 2) α₁ α₂ α₃ r).pow_const (-q)
  have hdb := hd r hr hrh.le
  rw [sub_add_cancel] at hdb
  refine (rooted_set_weight_le P X hX γ hγ hγ₂ M hM measurableSet_ball
    (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ 0) hG
    (C := ENNReal.ofReal (Cr * r ^ δ)) ?_).trans ((mul_le_mul' le_rfl hdb).trans_eq ?_)
  · intro x hx
    exact hb r hr hrr x ((by simpa [Metric.mem_ball] using hx : ‖x‖ < r).le)
  · rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [add_comm κ δ, Real.rpow_add hr]
    ring

end DOZZ.Proofs
