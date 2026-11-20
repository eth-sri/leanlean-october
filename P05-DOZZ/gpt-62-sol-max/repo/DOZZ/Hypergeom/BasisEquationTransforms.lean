/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisEquationSource

/-! The unpowered local solution at one solves the Gauss equation by reflection. -/

@[expose] public section

namespace DOZZ.Proofs

theorem hasDerivAt_gaussReflect {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f (1 - z)) :
    HasDerivAt (fun w => f (1 - w)) (-deriv f (1 - z)) z := by
  simpa [Function.comp_def] using hf.hasDerivAt.comp z ((hasDerivAt_id z).const_sub (1 : ℂ))

private theorem gaussHolomorphicOperator_reflect (a b c : ℂ) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane) (h : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b (1 + a + b - c) f z = 0) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (fun w => f (1 - w)) z = 0 := by
  have hd : gaussCutPlane.EqOn (deriv (fun w => f (1 - w))) (fun w => -deriv f (1 - w)) :=
    fun z hz => (hasDerivAt_gaussReflect (hf _ (one_sub_gaussCutPlane_subset_gaussCutPlane hz)).differentiableAt).deriv
  intro z hz
  have hw := one_sub_gaussCutPlane_subset_gaussCutPlane hz
  have hd₂ := (hasDerivAt_gaussReflect (hf.deriv _ hw).differentiableAt).neg.deriv
  simp only [neg_neg] at hd₂
  change deriv (fun w => -deriv f (1 - w)) z = _ at hd₂
  rw [gaussHolomorphicOperator, hd.deriv gaussCutPlane_isOpen hz, hd₂, hd hz]
  have he := h _ hw
  dsimp [gaussHolomorphicOperator] at he
  linear_combination he

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
include hH

/-- The reflected unpowered local solution at one solves the Gauss equation. -/
theorem gaussGMinus_holomorphicOperator_eq_zero (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussGMinus H a b c) z = 0 := by
  rw [gaussGMinus_eq_reflect]
  have hc := one_add_a_add_b_sub_c_ne_int hδ
  exact gaussHolomorphicOperator_reflect a b c
    ((gaussFMinus_differentiableOn_cutPlane hH a b _ hc).analyticOnNhd gaussCutPlane_isOpen)
    (gaussFMinus_holomorphicOperator_eq_zero hH a b _ hc)

/-- The powered second local solution at zero solves the Gauss equation. -/
theorem gaussFPlus_holomorphicOperator_eq_zero (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussFPlus H a b c) z = 0 := by
  let δ := 1 - c
  let A := a - c + 1
  let B := b - c + 1
  let C := 2 - c
  let G := H A B C
  let P : ℂ → ℂ := fun z => z ^ δ
  let P₁ : ℂ → ℂ := fun z => δ * z ^ (δ - 1)
  let F := gaussFPlus H a b c
  have hC := two_sub_parameter_ne_nat_neg hc
  have hG := (hH A B C hC).1.analyticOnNhd gaussSlitPlane_isOpen
  have hd (z) (hz : z ∈ gaussCutPlane) : HasDerivAt P (P₁ z) z :=
    (Complex.hasStrictDerivAt_cpow_const (gaussCutPlane_subset_Complex_slitPlane hz)).hasDerivAt
  have hf : gaussCutPlane.EqOn (deriv F) (fun z => P₁ z * G z + P z * deriv G z) :=
    fun z hz => ((hd z hz).mul (hG z (gaussCutPlane_subset_gaussSlitPlane hz)).differentiableAt.hasDerivAt).deriv
  intro z hz
  have hs := gaussCutPlane_subset_Complex_slitPlane hz
  have hz0 := Complex.slitPlane_ne_zero hs
  have hg := hG z (gaussCutPlane_subset_gaussSlitPlane hz)
  have hg₁ := hG.deriv z (gaussCutPlane_subset_gaussSlitPlane hz)
  have hd₁ : HasDerivAt P₁ (δ * ((δ - 1) * z ^ (δ - 1 - 1))) z :=
    ((Complex.hasStrictDerivAt_cpow_const hs).hasDerivAt).const_mul δ
  have hf₂ := (((hd₁.mul hg.differentiableAt.hasDerivAt).add
    ((hd z hz).mul hg₁.differentiableAt.hasDerivAt)).deriv)
  change deriv (fun w => P₁ w * G w + P w * deriv G w) z = _ at hf₂
  change gaussHolomorphicOperator a b c F z = _
  rw [gaussHolomorphicOperator, hf.deriv gaussCutPlane_isOpen hz, hf₂, hf hz]
  have hpow₁ : z ^ (δ - 1) = P z / z := by simpa [P] using Complex.cpow_sub δ 1 hz0
  have hpow₂ : z ^ (δ - 1 - 1) = P z / z ^ 2 := by
    rw [show δ - 1 - 1 = δ - 2 by ring]
    simpa [P, Complex.cpow_two] using Complex.cpow_sub δ 2 hz0
  have he : gaussHolomorphicOperator A B C G z = 0 :=
    gauss_family_holomorphicOperator_eq_zero hH A B C hC z hz
  change z * (1 - z) * _ + (c - (a + b + 1) * z) * _ - a * b * (P z * G z) = 0
  dsimp only [P₁]
  rw [hpow₁, hpow₂]
  dsimp only [gaussHolomorphicOperator, δ, A, B, C] at he ⊢
  field_simp [hz0]
  linear_combination z * P z * he

/-- The powered second local solution at one solves the Gauss equation by reflection. -/
theorem gaussGPlus_holomorphicOperator_eq_zero (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussGPlus H a b c) z = 0 := by
  rw [gaussGPlus_eq_reflect]
  have hc := one_add_a_add_b_sub_c_ne_int hδ
  exact gaussHolomorphicOperator_reflect a b c
    ((gaussFPlus_differentiableOn_cutPlane hH a b _ hc).analyticOnNhd gaussCutPlane_isOpen)
    (gaussFPlus_holomorphicOperator_eq_zero hH a b _ hc)

end

end DOZZ.Proofs
