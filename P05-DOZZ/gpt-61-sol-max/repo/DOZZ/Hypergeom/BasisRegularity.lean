/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Germs
public import DOZZ.Hypergeom.ODE.CutPlaneTopology
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Holomorphy of the four transformed local Gauss basis functions. -/

public section

namespace DOZZ.Proofs

theorem gaussCutPlane_subset_gaussSlitPlane :
    gaussCutPlane ⊆ gaussSlitPlane := by
  intro z hz
  change z.im ≠ 0 ∨ z.re < 1
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  continuity

theorem gaussCutPlane_subset_Complex_slitPlane :
    gaussCutPlane ⊆ Complex.slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff]
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  continuity

private theorem one_sub_gaussCutPlane_subset_gaussSlitPlane :
    (fun z : ℂ => 1 - z) ⁻¹' gaussSlitPlane ⊇ gaussCutPlane := by
  intro z hz
  change (1 - z).im ≠ 0 ∨ (1 - z).re < 1
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  continuity

private theorem one_sub_gaussCutPlane_subset_Complex_slitPlane :
    (fun z : ℂ => 1 - z) ⁻¹' Complex.slitPlane ⊇ gaussCutPlane := by
  intro z hz
  change 1 - z ∈ Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  continuity

/-- Reflection across `1/2` preserves the common Gauss cut plane. -/
theorem one_sub_gaussCutPlane_subset_gaussCutPlane :
    (fun z : ℂ => 1 - z) ⁻¹' gaussCutPlane ⊇ gaussCutPlane := by
  intro z hz
  change 1 - z ∈ gaussCutPlane
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  rcases hz with him | ⟨hpos, hlt⟩
  · left
    simp_all
  · right
    simp_all

private theorem parameter_ne_nat_neg_of_ne_int {c : ℂ}
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) : ∀ n : ℕ, c ≠ -(n : ℂ) := by
  intro n heq
  apply hc (-(n : ℤ))
  exact heq.trans (by simp)

theorem two_sub_parameter_ne_nat_neg {c : ℂ}
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) : ∀ n : ℕ, 2 - c ≠ -(n : ℂ) := by
  intro n heq
  apply hc (n + 2)
  have hcast : c = (n : ℂ) + 2 := by
    grind
  exact_mod_cast hcast

theorem one_add_a_add_b_sub_c_ne_nat_neg {a b c : ℂ}
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ n : ℕ, 1 + a + b - c ≠ -(n : ℂ) := by
  intro n heq
  apply hδ (n + 1)
  have hcast : c - a - b = (n : ℂ) + 1 := by
    grind
  exact_mod_cast hcast

private theorem one_add_c_sub_a_sub_b_ne_nat_neg {a b c : ℂ}
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ n : ℕ, 1 + c - a - b ≠ -(n : ℂ) := by
  intro n heq
  apply hδ (-(n + 1))
  have hcast : c - a - b = -((n : ℂ) + 1) := by
    grind
  exact_mod_cast hcast

variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)

include H hH a b c in
/-- The first local solution at zero inherits holomorphy from the defining family. -/
theorem gaussFMinus_differentiableOn_cutPlane
     (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    DifferentiableOn ℂ (gaussFMinus H a b c) gaussCutPlane := ((hH a b c (parameter_ne_nat_neg_of_ne_int hc)).1).mono
    gaussCutPlane_subset_gaussSlitPlane

include H hH a b c in
/-- The powered second local solution at zero is holomorphic on the common cut plane. -/
theorem gaussFPlus_differentiableOn_cutPlane
     (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    DifferentiableOn ℂ (gaussFPlus H a b c) gaussCutPlane := by
  have htrans := hH (a - c + 1) (b - c + 1) (2 - c)
    (two_sub_parameter_ne_nat_neg hc)
  have hpow : DifferentiableOn ℂ (fun z : ℂ => z ^ (1 - c)) gaussCutPlane :=
    differentiableOn_id.cpow_const (fun z hz => gaussCutPlane_subset_Complex_slitPlane hz)
  have htransOn  :=
    htrans.1.mono gaussCutPlane_subset_gaussSlitPlane
  exact hpow.mul htransOn

include H hH a b c in
/-- The first local solution at one is holomorphic on the common cut plane. -/
theorem gaussGMinus_differentiableOn_cutPlane
     (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    DifferentiableOn ℂ (gaussGMinus H a b c) gaussCutPlane := by
  have htrans := hH a b (1 + a + b - c)
    (one_add_a_add_b_sub_c_ne_nat_neg hδ)
  have harg : DifferentiableOn ℂ (fun z : ℂ => 1 - z) gaussCutPlane := by
    fun_prop
  have htransOn  :=
    htrans.1.comp harg one_sub_gaussCutPlane_subset_gaussSlitPlane
  continuity

include H hH a b c in
/-- The powered second local solution at one is holomorphic on the common cut plane. -/
theorem gaussGPlus_differentiableOn_cutPlane
     (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    DifferentiableOn ℂ (gaussGPlus H a b c) gaussCutPlane := by
  have htrans := hH (c - b) (c - a) (1 + c - a - b)
    (one_add_c_sub_a_sub_b_ne_nat_neg hδ)
  have harg : DifferentiableOn ℂ (fun z : ℂ => 1 - z) gaussCutPlane := by
    fun_prop
  have hpow : DifferentiableOn ℂ (fun z : ℂ => (1 - z) ^ (c - a - b))
      gaussCutPlane := harg.cpow_const one_sub_gaussCutPlane_subset_Complex_slitPlane
  have htransOn  :=
    htrans.1.comp harg one_sub_gaussCutPlane_subset_gaussSlitPlane
  exact hpow.mul htransOn

end DOZZ.Proofs
