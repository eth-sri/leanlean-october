/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisEquationSource

/-! The unpowered local solution at one solves the Gauss equation by reflection. -/

@[expose] public section

namespace DOZZ.Proofs

variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}


private theorem gaussSlitPlane_isOpen_for_basis : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

section
variable (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
include hH a b c

/-- The reflected unpowered local solution at one solves the Gauss equation. -/
theorem gaussGMinus_holomorphicOperator_eq_zero
 (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussGMinus H a b c) z = 0 := by
  let c' := 1 + a + b - c
  let g := H a b c'
  let f := gaussGMinus H a b c
  have hc' : ∀ n : ℕ, c' ≠ -(n : ℂ) := by
    simpa [c'] using one_add_a_add_b_sub_c_ne_nat_neg hδ
  have hAnal : AnalyticOnNhd ℂ g gaussSlitPlane := by
    simpa [g] using (hH a b c' hc').1.analyticOnNhd gaussSlitPlane_isOpen_for_basis
  have hAnal' := hAnal.deriv
  have hAnal'' := hAnal'.deriv
  have hmap (z : ℂ) : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hderivEq : gaussCutPlane.EqOn (deriv f) (fun z => -deriv g (1 - z)) := by
    intro z hz
    have hw := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    change deriv (fun w => g (1 - w)) z = -deriv g (1 - z)
    simpa [g, Function.comp_def, mul_comm] using ((hAnal (1 - z) (gaussCutPlane_subset_gaussSlitPlane hw)).differentiableAt.hasDerivAt.comp z (hmap z)).deriv
  have hderiv2Eq : gaussCutPlane.EqOn (deriv (deriv f))
      (fun z => deriv (deriv g) (1 - z)) := by
    intro z hz
    have hw := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    refine (hderivEq.deriv gaussCutPlane_isOpen hz).trans (?_)
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using (((hAnal' (1 - z) (gaussCutPlane_subset_gaussSlitPlane hw)).differentiableAt.hasDerivAt.comp z (hmap z)).neg).deriv
  intro z hz
  let w := 1 - z
  have hw : w ∈ gaussCutPlane := by simpa [w] using
    one_sub_gaussCutPlane_subset_gaussCutPlane hz
  have hEqOp : gaussHolomorphicOperator a b c f z =
      gaussHolomorphicOperator a b c' g w := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator,
      hderiv2Eq hz, hderivEq hz]
    dsimp [f, g, w, c', gaussGMinus]
    ring
  rw [hEqOp]
  simpa [g, c'] using gauss_family_holomorphicOperator_eq_zero hH a b c' hc' w hw

/-- The powered second local solution at zero solves the Gauss equation. -/
theorem gaussFPlus_holomorphicOperator_eq_zero
 (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussFPlus H a b c) z = 0 := by
  let δ := 1 - c
  let A := a - c + 1
  let B := b - c + 1
  let C := 2 - c
  let P : ℂ → ℂ := fun z => z ^ δ
  let P₁ : ℂ → ℂ := fun z => δ * z ^ (δ - 1)
  let P₂ : ℂ → ℂ := fun z => δ * (δ - 1) * z ^ (δ - 2)
  let G := H A B C
  let F := gaussFPlus H a b c
  have hCfree : ∀ n : ℕ, C ≠ -(n : ℂ) := by
    simpa [C] using two_sub_parameter_ne_nat_neg hc
  have hGanalytic : AnalyticOnNhd ℂ G gaussSlitPlane := by
    simpa [G] using (hH A B C hCfree).1.analyticOnNhd gaussSlitPlane_isOpen_for_basis
  have hPdiff : DifferentiableOn ℂ P gaussCutPlane := by
    change DifferentiableOn ℂ (fun z : ℂ => z ^ δ) gaussCutPlane
    exact differentiableOn_id.cpow_const gaussCutPlane_subset_Complex_slitPlane
  have hP₁diff : DifferentiableOn ℂ P₁ gaussCutPlane := by
    change DifferentiableOn ℂ (fun z : ℂ => δ * z ^ (δ - 1)) gaussCutPlane
    exact (differentiableOn_const δ).mul
      (differentiableOn_id.cpow_const gaussCutPlane_subset_Complex_slitPlane)
  have hP₁eq : gaussCutPlane.EqOn (deriv P) P₁ := by
    intro z hz
    have hzslit := gaussCutPlane_subset_Complex_slitPlane hz
    simpa [P, P₁] using (Complex.deriv_cpow_const (c := δ) hzslit)
  have hP₂eq : gaussCutPlane.EqOn (deriv P₁) P₂ := by
    intro z hz
    have hzslit := gaussCutPlane_subset_Complex_slitPlane hz
    have hexp : δ - 1 - 1 = δ - 2 := by ring
    change deriv (fun w => δ * w ^ (δ - 1)) z = δ * (δ - 1) * z ^ (δ - 2)
    rw [deriv_const_mul_field δ, Complex.deriv_cpow_const (c := δ - 1) hzslit, hexp]
    ring
  have hF₁eq : gaussCutPlane.EqOn (deriv F)
      (fun z => P₁ z * G z + P z * deriv G z) := by
    intro z hz
    have hzslit := gaussCutPlane_subset_gaussSlitPlane hz
    change deriv (P * G) z = P₁ z * G z + P z * deriv G z
    rw [(((hPdiff z hz).differentiableAt (gaussCutPlane_isOpen.mem_nhds hz)).hasDerivAt.mul ((hGanalytic z hzslit).differentiableAt).hasDerivAt).deriv, hP₁eq hz]
  intro z hz
  have hz0 := (gaussCutPlane_subset_regularPlane hz).1
  have hzslit := gaussCutPlane_subset_gaussSlitPlane hz
  have hsumDeriv : deriv (fun w => P₁ w * G w + P w * deriv G w) z =
      P₂ z * G z + P₁ z * deriv G z + P₁ z * deriv G z + P z * deriv (deriv G) z := by
    have hleft := ((hP₁diff z hz).differentiableAt (gaussCutPlane_isOpen.mem_nhds hz)).hasDerivAt.mul ((hGanalytic z hzslit).differentiableAt).hasDerivAt
    have hleft' := (hleft.add (((hPdiff z hz).differentiableAt (gaussCutPlane_isOpen.mem_nhds hz)).hasDerivAt.mul (((hGanalytic.deriv) z hzslit).differentiableAt).hasDerivAt)).deriv
    rw [hP₂eq hz, hP₁eq hz] at hleft'
    have hfun : (fun w => P₁ w * G w + P w * deriv G w) =
        P * deriv G + P₁ * G := by
      funext w
      change P₁ w * G w + P w * deriv G w =
        P w * deriv G w + P₁ w * G w
      ring
    rw [hfun]
    rw [add_comm (P * deriv G) (P₁ * G), hleft']
    ring
  have : z ^ (δ - 1) = z ^ δ / z := by
    simpa using Complex.cpow_sub δ 1 hz0
  have : z ^ (δ - 2) = z ^ δ / z ^ 2 := by
    simpa [Complex.cpow_two] using Complex.cpow_sub δ 2 hz0
  have hP₁val : P₁ z = δ * P z / z := by grind
  have hP₂val : P₂ z = δ * (δ - 1) * P z / z ^ 2 := by grind
  have hFval : F z = P z * G z := by rfl
  have hEqOp : gaussHolomorphicOperator a b c F z =
      P z * gaussHolomorphicOperator A B C G z := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator, hF₁eq.deriv gaussCutPlane_isOpen hz]
    change z * (1 - z) * deriv (fun w => P₁ w * G w + P w * deriv G w) z +
      (c - (a + b + 1) * z) * deriv F z - a * b * F z =
      P z * (z * (1 - z) * deriv (deriv G) z +
        (C - (A + B + 1) * z) * deriv G z - A * B * G z)
    rw [hsumDeriv, hF₁eq hz, hFval, hP₁val, hP₂val]
    simp only [hP₁val]
    dsimp [A, B, C, δ]
    field_simp [hz0]
    ring_nf
  rw [hEqOp]
  simp [gauss_family_holomorphicOperator_eq_zero hH A B C hCfree z hz, G, A, B, C]

/-- The powered second local solution at one solves the Gauss equation by reflection. -/
theorem gaussGPlus_holomorphicOperator_eq_zero
 (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussGPlus H a b c) z = 0 := by
  let c₀ := 1 + a + b - c
  let A := a - c₀ + 1
  let B := b - c₀ + 1
  let C := 2 - c₀
  let P : ℂ → ℂ := fun z => z ^ (1 - c₀)
  let G := H A B C
  let g := gaussFPlus H a b c₀
  let f := gaussGPlus H a b c
  have hc₀ : ∀ n : ℤ, c₀ ≠ (n : ℂ) := by
    intro n heq
    have hshift : c - a - b = (1 - n : ℤ) := by
      have hδ₀ : c - a - b = 1 - c₀ := by dsimp [c₀]; ring
      rw [hδ₀, heq]
      push_cast
      ring
    exact hδ (1 - n) hshift
  have hCfree : ∀ n : ℕ, C ≠ -(n : ℂ) := by
    simpa [C] using two_sub_parameter_ne_nat_neg hc₀
  have hGanalytic : AnalyticOnNhd ℂ G gaussCutPlane := ((hH A B C hCfree).1.analyticOnNhd gaussSlitPlane_isOpen_for_basis).mono
      gaussCutPlane_subset_gaussSlitPlane
  have hPanalytic : AnalyticOnNhd ℂ P gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z : ℂ => z ^ (1 - c₀)) gaussCutPlane
    exact analyticOnNhd_id.cpow analyticOnNhd_const
      (fun z hz => gaussCutPlane_subset_Complex_slitPlane hz)
  have hganalytic : AnalyticOnNhd ℂ g gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => P z * G z) gaussCutPlane
    exact hPanalytic.mul hGanalytic
  have hmap (z : ℂ) : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hident : f = (fun z => g (1 - z)) := by
    funext z
    change (1 - z) ^ (c - a - b) * H (c - b) (c - a) (1 + c - a - b) (1 - z) =
      (1 - z) ^ (1 - c₀) * H (a - c₀ + 1) (b - c₀ + 1) (2 - c₀) (1 - z)
    have he : c - a - b = 1 - c₀ := by dsimp [c₀]; ring
    have ha : c - b = a - c₀ + 1 := by dsimp [c₀]; ring
    have hb : c - a = b - c₀ + 1 := by dsimp [c₀]; ring
    have hc : 1 + c - a - b = 2 - c₀ := by dsimp [c₀]; ring
    rw [he, ha, hb, hc]
  have hderivEq : gaussCutPlane.EqOn (deriv f) (fun z => -deriv g (1 - z)) := by
    intro z hz
    have hw := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    calc
      deriv f z = deriv (fun w => g (1 - w)) z := by rw [hident]
      _ = -deriv g (1 - z) := by
        simpa [Function.comp_def, mul_comm] using ((hganalytic (1 - z) hw).differentiableAt.hasDerivAt.comp z (hmap z)).deriv
  have hderiv₂Eq : gaussCutPlane.EqOn (deriv (deriv f))
      (fun z => deriv (deriv g) (1 - z)) := by
    intro z hz
    have hw := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    refine (hderivEq.deriv gaussCutPlane_isOpen hz).trans (?_)
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using ((((hganalytic.deriv) (1 - z) hw).differentiableAt.hasDerivAt.comp z (hmap z)).neg).deriv
  intro z hz
  let w := 1 - z
  have hw : w ∈ gaussCutPlane := by simpa [w] using
    one_sub_gaussCutPlane_subset_gaussCutPlane hz
  have hEqOp : gaussHolomorphicOperator a b c f z =
      gaussHolomorphicOperator a b c₀ g w := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator,
      hderiv₂Eq hz, hderivEq hz, hident]
    dsimp [w, c₀]
    ring
  rw [hEqOp]
  simpa [g] using gaussFPlus_holomorphicOperator_eq_zero hH a b c₀ hc₀ w hw


end
end DOZZ.Proofs
