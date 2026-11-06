/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ExtendedSeiberg3

/-! # Parameter windows for the two fusion limits -/

@[expose] public section
namespace DOZZ.Proofs

/-- The fusion exponent is the scaling degree of the planar integral. -/
theorem fusion_exponent_eq (γ α₁ : ℝ) (hγ : γ ≠ 0) :
    γ * (Q γ - α₁) = 2 + γ ^ 2 / 2 - γ * α₁ := by
  unfold Q
  field_simp

/-- The Taylor domain supplies the subtracted planar-integral window and `κ < 2`. -/
theorem fusion_taylor_parameters (γ α₁ : ℝ) (hγ : 0 < γ)
    (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hhi : α₁ < 2 / γ) :
    0 < γ ^ 2 / 2 ∧ γ ^ 2 / 2 < γ * α₁ ∧ γ * α₁ < 2 ∧
      γ * α₁ < γ ^ 2 / 2 + 1 ∧ 0 < γ * (Q γ - α₁) ∧
      γ * (Q γ - α₁) < 2 := by
  have hβ : γ * α₁ < 2 := by
    have := (lt_div_iff₀ hγ).mp hhi
    nlinarith
  rw [fusion_exponent_eq γ α₁ hγ.ne']
  refine ⟨by positivity, by nlinarith, hβ, by linarith, by nlinarith, by nlinarith⟩

/-- The restricted KRV domain supplies the unsubtracted difference window and `κ < 1`. -/
theorem fusion_difference_parameters (γ α₁ : ℝ) (hγ : 0 < γ)
    (hlo : γ / 2 + 1 / γ < α₁) (hhi : α₁ < 2 / γ) :
    0 < γ ^ 2 / 2 ∧ γ ^ 2 / 2 + 1 < γ * α₁ ∧ γ * α₁ < 2 ∧
      0 < γ * (Q γ - α₁) ∧ γ * (Q γ - α₁) < 1 := by
  have hβ : γ * α₁ < 2 := by
    have := (lt_div_iff₀ hγ).mp hhi
    nlinarith
  have hlo' := mul_lt_mul_of_pos_left hlo hγ
  have he : γ * (γ / 2 + 1 / γ) = γ ^ 2 / 2 + 1 := by
    field_simp
  rw [he] at hlo'
  rw [fusion_exponent_eq γ α₁ hγ.ne']
  exact ⟨by positivity, hlo', hβ, by nlinarith, by linarith⟩

end DOZZ.Proofs
