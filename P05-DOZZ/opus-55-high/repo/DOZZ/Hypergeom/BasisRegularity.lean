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
  tauto

theorem gaussCutPlane_subset_Complex_slitPlane :
    gaussCutPlane ⊆ Complex.slitPlane := by
  intro z hz
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  tauto

private theorem one_sub_gaussCutPlane_subset_gaussSlitPlane :
    (fun z : ℂ => 1 - z) ⁻¹' gaussSlitPlane ⊇ gaussCutPlane := by
  intro z hz
  change (1 - z).im ≠ 0 ∨ (1 - z).re < 1
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  aesop

private theorem one_sub_gaussCutPlane_subset_Complex_slitPlane :
    (fun z : ℂ => 1 - z) ⁻¹' Complex.slitPlane ⊇ gaussCutPlane := by
  intro z hz
  change 1 - z ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  aesop

/-- Reflection across `1/2` preserves the common Gauss cut plane. -/
theorem one_sub_gaussCutPlane_subset_gaussCutPlane :
    (fun z : ℂ => 1 - z) ⁻¹' gaussCutPlane ⊇ gaussCutPlane := by
  intro z hz
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  rcases hz with him | ⟨hpos, hlt⟩
  · left
    simp_all
  · right
    simp_all
section
variable {c : ℂ}
section
variable (hc : ∀ n : ℤ, c ≠ (n : ℂ))
include hc

private theorem parameter_ne_nat_neg_of_ne_int : ∀ n : ℕ, c ≠ -(n : ℂ) := by
  intro n heq
  apply hc (-n)
  simp_all

theorem two_sub_parameter_ne_nat_neg : ∀ n : ℕ, 2 - c ≠ -(n : ℂ) := by
  intro n heq
  apply hc _
  have hcast : c = n + 2 := by
    grind
  exact_mod_cast hcast

end

end
section
variable {a b c : ℂ}
section
variable (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ))
include hδ

theorem one_add_a_add_b_sub_c_ne_nat_neg :
    ∀ n : ℕ, 1 + a + b - c ≠ -(n : ℂ) := by
  intro n heq
  apply hδ _
  have hcast : c - a - b = n + 1 := by
    grind
  exact_mod_cast hcast

private theorem one_add_c_sub_a_sub_b_ne_nat_neg :
    ∀ n : ℕ, 1 + c - a - b ≠ -(n : ℂ) := by
  intro n heq
  apply hδ _
  have hcast : c - a - b = -(n + 1) := by
    grind
  exact_mod_cast hcast

end

end
section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}
section
variable (hH : IsGaussHypergeometricFamily H) (a b c : ℂ) (hc : ∀ n : ℤ, c ≠ (n : ℂ))
include hH hc

/-- The first local solution at zero inherits holomorphy from the defining family. -/
theorem gaussFMinus_differentiableOn_cutPlane
    :
    DifferentiableOn ℂ (gaussFMinus H a b c) gaussCutPlane := by
  exact ((hH a b c (parameter_ne_nat_neg_of_ne_int hc)).1).mono
    gaussCutPlane_subset_gaussSlitPlane

/-- The powered second local solution at zero is holomorphic on the common cut plane. -/
theorem gaussFPlus_differentiableOn_cutPlane
    :
    DifferentiableOn ℂ (gaussFPlus H a b c) gaussCutPlane := by
  have htrans := hH (a - c + 1) (b - c + 1) _
    (two_sub_parameter_ne_nat_neg hc)
  have hpow : DifferentiableOn ℂ (fun z => z ^ (1 - c)) gaussCutPlane :=
    differentiableOn_id.cpow_const (fun z hz => gaussCutPlane_subset_Complex_slitPlane hz)
  have htransOn :=
    htrans.1.mono gaussCutPlane_subset_gaussSlitPlane
  change DifferentiableOn ℂ
    (fun z => z ^ (1 - c) * H _ _ _ z) gaussCutPlane
  fun_prop

end
section
variable (hH : IsGaussHypergeometricFamily H) (a b c : ℂ) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ))
include hH hδ

/-- The first local solution at one is holomorphic on the common cut plane. -/
theorem gaussGMinus_differentiableOn_cutPlane
    :
    DifferentiableOn ℂ (gaussGMinus H a b c) gaussCutPlane := by
  have htrans := hH a b _
    (one_add_a_add_b_sub_c_ne_nat_neg hδ)
  have harg : DifferentiableOn ℂ (fun z => 1 - z) gaussCutPlane := by
    fun_prop
  exact 
    htrans.1.comp harg one_sub_gaussCutPlane_subset_gaussSlitPlane

/-- The powered second local solution at one is holomorphic on the common cut plane. -/
theorem gaussGPlus_differentiableOn_cutPlane
    :
    DifferentiableOn ℂ (gaussGPlus H a b c) gaussCutPlane := by
  have htrans := hH (c - b) (c - a) _
    (one_add_c_sub_a_sub_b_ne_nat_neg hδ)
  have harg : DifferentiableOn ℂ (fun z => 1 - z) gaussCutPlane := by
    fun_prop
  have hpow : DifferentiableOn ℂ (fun z => (1 - z) ^ (c - a - b))
      gaussCutPlane := harg.cpow_const one_sub_gaussCutPlane_subset_Complex_slitPlane
  have htransOn :=
    htrans.1.comp harg one_sub_gaussCutPlane_subset_gaussSlitPlane
  change DifferentiableOn ℂ
    (fun z => (1 - z) ^ (c - a - b) *
      H ..) gaussCutPlane
  exact hpow.mul htransOn

end

end

end DOZZ.Proofs
