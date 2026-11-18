/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.Domain
import Mathlib.Tactic

/-! # The corrected dual fusion window

The annular power may lie on either side of the logarithmic threshold 3.
-/

public section

namespace DOZZ.Proofs

/-- The near-Q premises supply every scalar margin used in dual fusion. -/
theorem dual_window_margins (γ α η ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hη : 0 < η) (hη₂ : η < γ / 2)
    (hξ₂ : ξ < 1) (hαlo : Q γ - η < α) (hαhi : α < Q γ)
    (hslack₁ : (4 / γ) * (Q γ - α) < ξ)
    (hslack₂ : (4 / γ) * (Q γ - α) <
      (1 - ξ) * (4 - γ * α - 2 * γ * η)) :
    0 < Q γ - α ∧ Q γ - α < γ / 2 ∧
      0 < (4 / γ) * (Q γ - α) ∧ (4 / γ) * (Q γ - α) < 1 ∧
      (4 / γ) * (Q γ - α) < (1 - ξ) * (4 - γ * α) ∧
      2 < γ * α ∧ γ * α < 2 + γ ^ 2 / 2 ∧
      0 < 4 - γ * α ∧ γ * (Q γ - α) < 2 ∧
      (4 / γ) * (Q γ - α) < 2 - γ ^ 2 / 2 + γ * (Q γ - α) := by
  have hν := sub_pos.mpr hαhi
  have hνη : Q γ - α < η := by nlinarith
  have hκ : 0 < (4 / γ) * (Q γ - α) :=
    mul_pos (div_pos (by norm_num) hγ) hν
  have : γ * Q γ = 2 + γ ^ 2 / 2 := by
    unfold Q
    field_simp
  have hγsq : γ ^ 2 < 4 := by nlinarith
  have hνmul : γ * (Q γ - α) < γ ^ 2 / 2 := by nlinarith
  have hαmul : 2 < γ * α := by nlinarith
  have hαmul₂ : γ * α < 2 + γ ^ 2 / 2 := by nlinarith
  have houter : (4 / γ) * (Q γ - α) < (1 - ξ) * (4 - γ * α) := by
    have hbuffer : 0 < (1 - ξ) * (2 * γ * η) :=
      mul_pos (sub_pos.mpr hξ₂) (mul_pos (mul_pos (by norm_num) hγ) hη)
    nlinarith only [hslack₂, hbuffer]
  have hfirst : (4 / γ) * (Q γ - α) <
      2 - γ ^ 2 / 2 + γ * (Q γ - α) := by nlinarith
  exact ⟨hν, hνη.trans hη₂, hκ, hslack₁.trans hξ₂, houter, hαmul, hαmul₂,
    by linarith only [hαmul₂, hγsq], by linarith only [hνmul, hγsq], hfirst⟩

/-- The dual reflected triple is ordinary Seiberg on the explicit near-Q window. -/
theorem dual_window_reflected_triple (γ α₁ α₂ α₃ η : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hη₂ : η < γ / 2)
    (hαlo : Q γ - η < α₁) (hαhi : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃) :
    2 * Q γ - α₁ - 2 / γ < Q γ ∧
      α₂ < Q γ ∧ α₃ < Q γ ∧
      2 * Q γ < (2 * Q γ - α₁ - 2 / γ) + α₂ + α₃ := by
  have hd : γ / 2 < 2 / γ := by
    apply (lt_div_iff₀ hγ).2
    nlinarith only [hγ, hγ₂]
  refine ⟨?_, hα₂, hα₃, ?_⟩
  · linarith only [hαlo, hη₂, hd]
  · linarith only [hs, hαhi]

/-- The dual reflection exponent is twice the maximum-tail exponent. -/
theorem dual_window_zero_mode_order (γ α₁ α₂ α₃ : ℝ) :
    ((2 * Q γ - α₁ - 2 / γ) + α₂ + α₃ - 2 * Q γ) / γ =
      (α₁ + α₂ + α₃ - 2 / γ - 2 * Q γ) / γ +
        2 * (Q γ - α₁) / γ := by
  ring

end DOZZ.Proofs
