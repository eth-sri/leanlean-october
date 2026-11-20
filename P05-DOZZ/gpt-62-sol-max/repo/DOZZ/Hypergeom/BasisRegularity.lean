/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Germs
public import DOZZ.Hypergeom.ODE.CutPlaneTopology
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Holomorphy of the four transformed local Gauss basis functions. -/

@[expose] public section

namespace DOZZ.Proofs

theorem gaussCutPlane_subset_gaussSlitPlane :
    gaussCutPlane ⊆ gaussSlitPlane := by
  intro z hz
  change z.im ≠ 0 ∨ z.re < 1
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  rcases hz with him | ⟨_, hlt⟩
  · exact Or.inl him
  · exact Or.inr hlt

theorem gaussCutPlane_subset_Complex_slitPlane :
    gaussCutPlane ⊆ Complex.slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  rcases hz with him | ⟨hpos, _⟩
  · exact Or.inr him
  · exact Or.inl hpos

/-- Reflection across `1/2` preserves the common Gauss cut plane. -/
theorem one_sub_gaussCutPlane_subset_gaussCutPlane :
    (fun z : ℂ => 1 - z) ⁻¹' gaussCutPlane ⊇ gaussCutPlane := by
  intro z hz
  change 1 - z ∈ gaussCutPlane
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  rcases hz with him | ⟨hpos, hlt⟩
  · left
    simpa
  · right
    simp [*]

section
variable {c : ℂ} (hc : ∀ n : ℤ, c ≠ (n : ℂ))
include hc

theorem parameter_ne_nat_neg_of_ne_int : ∀ n : ℕ, c ≠ -(n : ℂ) := by
  intro n heq
  apply hc (-(n : ℤ))
  simpa

theorem two_sub_parameter_ne_nat_neg : ∀ n : ℕ, 2 - c ≠ -(n : ℂ) := by
  intro n heq
  apply hc (n + 2)
  have hcast : c = (n : ℂ) + 2 := by
    grind
  exact_mod_cast hcast

end

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
  (hc : ∀ n : ℤ, c ≠ (n : ℂ))
include hH hc

/-- The first local solution at zero inherits holomorphy from the defining family. -/
theorem gaussFMinus_differentiableOn_cutPlane :
    DifferentiableOn ℂ (gaussFMinus H a b c) gaussCutPlane := by
  change DifferentiableOn ℂ (H a b c) gaussCutPlane
  exact ((hH a b c (parameter_ne_nat_neg_of_ne_int hc)).1).mono
    gaussCutPlane_subset_gaussSlitPlane

/-- The powered second local solution at zero is holomorphic on the common cut plane. -/
theorem gaussFPlus_differentiableOn_cutPlane :
    DifferentiableOn ℂ (gaussFPlus H a b c) gaussCutPlane := by
  have htrans := hH (a - c + 1) (b - c + 1) (2 - c)
    (two_sub_parameter_ne_nat_neg hc)
  have hpow : DifferentiableOn ℂ (fun z : ℂ => z ^ (1 - c)) gaussCutPlane :=
    differentiableOn_id.cpow_const (fun z hz => gaussCutPlane_subset_Complex_slitPlane hz)
  have htransOn := htrans.1.mono gaussCutPlane_subset_gaussSlitPlane
  apply hpow.mul <;> assumption

end

theorem one_add_a_add_b_sub_c_ne_int {a b c : ℂ}
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) : ∀ n : ℤ, 1 + a + b - c ≠ (n : ℂ) := by
  intro n h
  apply hδ (1 - n)
  push_cast
  linear_combination -h

section
variable (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c : ℂ)

theorem gaussGMinus_eq_reflect :
    gaussGMinus H a b c = fun z => gaussFMinus H a b (1 + a + b - c) (1 - z) := rfl

theorem gaussGPlus_eq_reflect :
    gaussGPlus H a b c = fun z => gaussFPlus H a b (1 + a + b - c) (1 - z) := by
  funext z
  simp only [gaussGPlus, gaussFPlus]
  congr 2 <;> ring

end

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
  (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ))
include hH hδ

/-- The first local solution at one is holomorphic on the common cut plane. -/
theorem gaussGMinus_differentiableOn_cutPlane :
    DifferentiableOn ℂ (gaussGMinus H a b c) gaussCutPlane := by
  rw [gaussGMinus_eq_reflect]
  exact (gaussFMinus_differentiableOn_cutPlane hH a b _ (one_add_a_add_b_sub_c_ne_int hδ)).comp
    (by fun_prop) one_sub_gaussCutPlane_subset_gaussCutPlane

/-- The powered second local solution at one is holomorphic on the common cut plane. -/
theorem gaussGPlus_differentiableOn_cutPlane :
    DifferentiableOn ℂ (gaussGPlus H a b c) gaussCutPlane := by
  rw [gaussGPlus_eq_reflect]
  exact (gaussFPlus_differentiableOn_cutPlane hH a b _ (one_add_a_add_b_sub_c_ne_int hδ)).comp
    (by fun_prop) one_sub_gaussCutPlane_subset_gaussCutPlane

end

end DOZZ.Proofs
