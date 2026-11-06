/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisEquationSource

/-! The unpowered local solution at one solves the Gauss equation by reflection. -/

@[expose] public section

namespace DOZZ.Proofs

private theorem gaussSlitPlane_isOpen_for_basis : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

/-- The reflected unpowered local solution at one solves the Gauss equation. -/
theorem gaussGMinus_holomorphicOperator_eq_zero
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussGMinus H a b c) z = 0 := by
  let c' := 1 + a + b - c
  let g := H a b c'
  let f := gaussGMinus H a b c
  have hc' : ∀ n : ℕ, c' ≠ -(n : ℂ) := by
    simpa [c'] using one_add_a_add_b_sub_c_ne_nat_neg hδ
  have hAnal : AnalyticOnNhd ℂ g gaussSlitPlane := by
    simpa [g] using (hH a b c' hc').1.analyticOnNhd gaussSlitPlane_isOpen_for_basis
  have hmap (z : ℂ) : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hderivEq : gaussCutPlane.EqOn (deriv f) (fun z => -deriv g (1 - z)) := by
    intro z hz
    change deriv (fun w => g (1 - w)) z = -deriv g (1 - z)
    simpa [g, Function.comp_def, mul_comm] using ((hAnal (1 - z) (gaussCutPlane_subset_gaussSlitPlane (one_sub_gaussCutPlane_subset_gaussCutPlane hz))).differentiableAt.hasDerivAt.comp z (hmap z)).deriv
  have hderiv2Eq : gaussCutPlane.EqOn (deriv (deriv f))
      (fun z => deriv (deriv g) (1 - z)) := by
    intro z hz
    calc
      deriv (deriv f) z = deriv (fun w => -deriv g (1 - w)) z := (hderivEq.deriv gaussCutPlane_isOpen hz)
      _ = deriv (deriv g) (1 - z) := by
        simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using ((hAnal.deriv (1 - z) (gaussCutPlane_subset_gaussSlitPlane (one_sub_gaussCutPlane_subset_gaussCutPlane hz))).differentiableAt.hasDerivAt.comp z (hmap z)).neg.deriv
  intro z hz
  let w := 1 - z
  have hEqOp : gaussHolomorphicOperator a b c f z =
      gaussHolomorphicOperator a b c' g w := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator,
      hderiv2Eq hz, hderivEq hz]
    dsimp [f, g, w, c', gaussGMinus]
    ring
  rw [hEqOp]
  simpa [g, c'] using (gauss_family_holomorphicOperator_eq_zero hH a b c' hc') w (by simpa [w] using one_sub_gaussCutPlane_subset_gaussCutPlane hz)

/-- The powered second local solution at zero solves the Gauss equation. -/
theorem gaussFPlus_holomorphicOperator_eq_zero
    {H} (hH : IsGaussHypergeometricFamily H)
    a b c (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussFPlus H a b c) z = 0 := by
  let δ : ℂ := 1 - c
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
  have hGanalytic₁ := hGanalytic.deriv
  have hPdiff : DifferentiableOn ℂ P gaussCutPlane := by
    change DifferentiableOn ℂ (fun z : ℂ => z ^ δ) gaussCutPlane
    exact differentiableOn_id.cpow_const gaussCutPlane_subset_Complex_slitPlane
  have hP₁eq : gaussCutPlane.EqOn (deriv P) P₁ := by
    intro z hz
    simpa [P, P₁] using (Complex.deriv_cpow_const (c := δ) (gaussCutPlane_subset_Complex_slitPlane hz))
  have hP₂eq : gaussCutPlane.EqOn (deriv P₁) P₂ := by
    intro z hz
    change deriv (fun w => δ * w ^ (δ - 1)) z = δ * (δ - 1) * z ^ (δ - 2)
    rw [deriv_const_mul_field δ, (Complex.deriv_cpow_const (c := δ - 1) (gaussCutPlane_subset_Complex_slitPlane hz)), (show δ - 1 - 1 = δ - 2 by ring)]
    ring
  have hF₁eq : gaussCutPlane.EqOn (deriv F)
      (fun z => P₁ z * G z + P z * deriv G z) := by
    intro z hz
    change deriv (P * G) z = P₁ z * G z + P z * deriv G z
    rw [(((hPdiff z hz).differentiableAt (gaussCutPlane_isOpen.mem_nhds hz)).hasDerivAt.mul ((hGanalytic z (gaussCutPlane_subset_gaussSlitPlane hz)).differentiableAt).hasDerivAt).deriv, hP₁eq hz]
  intro z hz
  have hz0 := (gaussCutPlane_subset_regularPlane hz).1
  have hzslit := gaussCutPlane_subset_gaussSlitPlane hz
  have hsumDeriv : deriv (fun w => P₁ w * G w + P w * deriv G w) z =
      P₂ z * G z + P₁ z * deriv G z + P₁ z * deriv G z + P z * deriv (deriv G) z := by
    have hleft' := (((((show DifferentiableOn ℂ P₁ gaussCutPlane by change DifferentiableOn ℂ (fun z => δ * z ^ (δ - 1)) gaussCutPlane; exact (differentiableOn_const δ).mul (differentiableOn_id.cpow_const gaussCutPlane_subset_Complex_slitPlane)) z hz).differentiableAt (gaussCutPlane_isOpen.mem_nhds hz)).hasDerivAt.mul ((hGanalytic z hzslit).differentiableAt).hasDerivAt).add (((hPdiff z hz).differentiableAt (gaussCutPlane_isOpen.mem_nhds hz)).hasDerivAt.mul ((hGanalytic₁ z hzslit).differentiableAt).hasDerivAt)).deriv
    rw [hP₂eq hz, hP₁eq hz] at hleft'
    have hfun : (fun w => P₁ w * G w + P w * deriv G w) =
        P * deriv G + P₁ * G := by
      funext w
      change P₁ w * G w + P w * deriv G w =
        P w * deriv G w + P₁ w * G w
      ring
    rw [hfun, add_comm (P * deriv G) (P₁ * G), hleft']
    ring
  have hP₁val : P₁ z = δ * P z / z := by
    simp only [P₁, P]
    rw [(show z ^ (δ - 1) = z ^ δ / z by simpa using Complex.cpow_sub δ 1 hz0)]
    ring
  have hP₂val : P₂ z = δ * (δ - 1) * P z / z ^ 2 := by
    simp only [P₂, P]
    calc
      δ * (δ - 1) * z ^ (δ - 2) = δ * (δ - 1) * (z ^ δ / z ^ 2) :=
        congrArg (fun x : ℂ => δ * (δ - 1) * x) (by simpa [Complex.cpow_two] using Complex.cpow_sub δ 2 hz0)
      _ = δ * (δ - 1) * z ^ δ / z ^ 2 := by
        field_simp [hz0]
  have hEqOp : gaussHolomorphicOperator a b c F z =
      P z * gaussHolomorphicOperator A B C G z := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator, (hF₁eq.deriv gaussCutPlane_isOpen) hz]
    change z * (1 - z) * deriv (fun w => P₁ w * G w + P w * deriv G w) z +
      (c - (a + b + 1) * z) * deriv F z - a * b * F z =
      P z * (z * (1 - z) * deriv (deriv G) z +
        (C - (A + B + 1) * z) * deriv G z - A * B * G z)
    rw [hsumDeriv, hF₁eq hz, (show F z = P z * G z by simp [F, gaussFPlus, P, G, δ, A, B, C]), hP₁val, hP₂val]
    simp only [hP₁val]
    dsimp [A, B, C, δ]
    field_simp [hz0]
    ring_nf
  rw [hEqOp]
  simp [(gauss_family_holomorphicOperator_eq_zero hH A B C hCfree) z hz, G, A, B, C]

/-- The powered second local solution at one solves the Gauss equation by reflection. -/
theorem gaussGPlus_holomorphicOperator_eq_zero
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussGPlus H a b c) z = 0 := by
  let c₀ := 1 + a + b - c
  let A := a - c₀ + 1
  let B := b - c₀ + 1
  let C := 2 - c₀
  let P : ℂ → ℂ := fun z => z ^ (1 - c₀)
  let g := gaussFPlus H a b c₀
  let f := gaussGPlus H a b c
  have hc₀ : ∀ n : ℤ, c₀ ≠ (n : ℂ) := by
    intro n heq
    exact hδ (1 - n) (by rw [(show c - a - b = 1 - c₀ by dsimp [c₀]; ring), heq]; push_cast; ring)
  have hganalytic : AnalyticOnNhd ℂ g gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => P z * (H A B C) z) gaussCutPlane
    exact (show AnalyticOnNhd ℂ P gaussCutPlane by change AnalyticOnNhd ℂ (fun z : ℂ => z ^ (1 - c₀)) gaussCutPlane; exact analyticOnNhd_id.cpow analyticOnNhd_const (fun z hz => gaussCutPlane_subset_Complex_slitPlane hz)).mul (((hH A B C (by simpa [C] using two_sub_parameter_ne_nat_neg hc₀)).1.analyticOnNhd gaussSlitPlane_isOpen_for_basis).mono gaussCutPlane_subset_gaussSlitPlane)
  have hmap (z : ℂ) : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hident : f = (fun z => g (1 - z)) := by
    funext z
    change (1 - z) ^ (c - a - b) * H (c - b) (c - a) (1 + c - a - b) (1 - z) =
      (1 - z) ^ (1 - c₀) * H (a - c₀ + 1) (b - c₀ + 1) (2 - c₀) (1 - z)
    rw [(show c - a - b = 1 - c₀ by dsimp [c₀]; ring), (show c - b = a - c₀ + 1 by dsimp [c₀]; ring), (show c - a = b - c₀ + 1 by dsimp [c₀]; ring), (show 1 + c - a - b = 2 - c₀ by dsimp [c₀]; ring)]
  have hderivEq : gaussCutPlane.EqOn (deriv f) (fun z => -deriv g (1 - z)) := by
    intro z hz
    calc
      deriv f z = deriv (fun w => g (1 - w)) z := by rw [hident]
      _ = -deriv g (1 - z) := by
        simpa [Function.comp_def, mul_comm] using ((hganalytic (1 - z) (one_sub_gaussCutPlane_subset_gaussCutPlane hz)).differentiableAt.hasDerivAt.comp z (hmap z)).deriv
  have hderiv₂Eq : gaussCutPlane.EqOn (deriv (deriv f))
      (fun z => deriv (deriv g) (1 - z)) := by
    intro z hz
    calc
      deriv (deriv f) z = deriv (fun w => -deriv g (1 - w)) z := (hderivEq.deriv gaussCutPlane_isOpen hz)
      _ = deriv (deriv g) (1 - z) := by
        simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using ((hganalytic.deriv (1 - z) (one_sub_gaussCutPlane_subset_gaussCutPlane hz)).differentiableAt.hasDerivAt.comp z (hmap z)).neg.deriv
  intro z hz
  let w := 1 - z
  have hEqOp : gaussHolomorphicOperator a b c f z =
      gaussHolomorphicOperator a b c₀ g w := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator,
      hderiv₂Eq hz, hderivEq hz, hident]
    dsimp [w, c₀]
    ring
  rw [hEqOp]
  simpa [g] using (gaussFPlus_holomorphicOperator_eq_zero hH a b c₀ hc₀) w (by simpa [w] using one_sub_gaussCutPlane_subset_gaussCutPlane hz)

end DOZZ.Proofs
