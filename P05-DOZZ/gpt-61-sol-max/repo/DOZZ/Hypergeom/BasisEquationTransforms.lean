/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisEquationSource
import Mathlib.Tactic

/-! The unpowered local solution at one solves the Gauss equation by reflection. -/

public section

namespace DOZZ.Proofs

private theorem gaussSlitPlane_isOpen_for_basis : IsOpen gaussSlitPlane := (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)

include H hH a b c in
/-- The reflected unpowered local solution at one solves the Gauss equation. -/
theorem gaussGMinus_holomorphicOperator_eq_zero
     (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussGMinus H a b c) z = 0 := by
  let c'  := 1 + a + b - c
  let g  := H a b c'
  let f  := gaussGMinus H a b c
  have hc' : ∀ n : ℕ, c' ≠ -(n : ℂ) := one_add_a_add_b_sub_c_ne_nat_neg hδ
  have hsource := gauss_family_holomorphicOperator_eq_zero hH a b c' hc'
  have hAnal : AnalyticOnNhd ℂ g gaussSlitPlane := by
    have hchar := hH a b c' hc'
    exact hchar.1.analyticOnNhd gaussSlitPlane_isOpen_for_basis
  have hAnal'  := hAnal.deriv

  have hmap (z : ℂ) : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := (hasDerivAt_id z).const_sub (1 : ℂ)
  have hderivEq : gaussCutPlane.EqOn (deriv f) (fun z => -deriv g (1 - z)) := by
    intro z hz
    have hw  := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hwslit  := gaussCutPlane_subset_gaussSlitPlane hw
    have hcomp := (hAnal (1 - z) hwslit).differentiableAt.hasDerivAt.comp z (hmap z)
    change deriv (fun w => g (1 - w)) z = -deriv g (1 - z)
    simpa [g, Function.comp_def, mul_comm] using hcomp.deriv
  have hderiv2Eq : gaussCutPlane.EqOn (deriv (deriv f))
      (fun z => deriv (deriv g) (1 - z)) := by
    intro z hz
    have hfirst := hderivEq.deriv gaussCutPlane_isOpen hz
    have hw  := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hwslit  := gaussCutPlane_subset_gaussSlitPlane hw
    have hcomp := (hAnal' (1 - z) hwslit).differentiableAt.hasDerivAt.comp z (hmap z)
    have hneg := hcomp.neg
    calc
      deriv (deriv f) z = deriv (fun w => -deriv g (1 - w)) z := hfirst
      _ = deriv (deriv g) (1 - z) := by
        simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hneg.deriv
  intro z hz
  let w := 1 - z
  have hw : w ∈ gaussCutPlane := one_sub_gaussCutPlane_subset_gaussCutPlane hz
  have hEqOp : gaussHolomorphicOperator a b c f z =
      gaussHolomorphicOperator a b c' g w := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator,
      hderiv2Eq hz, hderivEq hz]
    dsimp [f, g, w, c', gaussGMinus]
    ring
  rw [hEqOp]
  exact hsource w hw

include H hH a b c in
/-- The powered second local solution at zero solves the Gauss equation. -/
theorem gaussFPlus_holomorphicOperator_eq_zero
     (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussFPlus H a b c) z = 0 := by
  let δ  := 1 - c
  let A  := a - c + 1
  let B  := b - c + 1
  let C  := 2 - c
  let P : ℂ → ℂ := fun z => z ^ δ
  let P₁  := fun z => δ * z ^ (δ - 1)
  let P₂  := fun z => δ * (δ - 1) * z ^ (δ - 2)
  let G  := H A B C
  let F  := gaussFPlus H a b c
  have hCfree : ∀ n : ℕ, C ≠ -(n : ℂ) := two_sub_parameter_ne_nat_neg hc
  have hsource := gauss_family_holomorphicOperator_eq_zero hH A B C hCfree
  have hGanalytic : AnalyticOnNhd ℂ G gaussSlitPlane := by
    have hchar := hH A B C hCfree
    exact hchar.1.analyticOnNhd gaussSlitPlane_isOpen_for_basis
  have hGanalytic₁  := hGanalytic.deriv

  have hPdiff : DifferentiableOn ℂ P gaussCutPlane := differentiableOn_id.cpow_const gaussCutPlane_subset_Complex_slitPlane
  have hP₁diff : DifferentiableOn ℂ P₁ gaussCutPlane := (differentiableOn_const δ).mul
      (differentiableOn_id.cpow_const gaussCutPlane_subset_Complex_slitPlane)
  have hP₁eq : gaussCutPlane.EqOn (deriv P) P₁ := fun ⦃z⦄ hz =>   have hzslit := gaussCutPlane_subset_Complex_slitPlane hz;   id (Complex.deriv_cpow_const hzslit)
  have hP₂eq : gaussCutPlane.EqOn (deriv P₁) P₂ := by
    intro z hz
    have hzslit := gaussCutPlane_subset_Complex_slitPlane hz
    have hpow := Complex.deriv_cpow_const (c := δ - 1) hzslit
    have hexp : δ - 1 - 1 = δ - 2 := by ring
    change deriv (fun w => δ * w ^ (δ - 1)) z = δ * (δ - 1) * z ^ (δ - 2)
    rw [deriv_const_mul_field δ, hpow, hexp]
    ring


  have hF₁eq : gaussCutPlane.EqOn (deriv F)
      (fun z => P₁ z * G z + P z * deriv G z) := by
    intro z hz
    have hPAt  :=
      (hPdiff z hz).differentiableAt (gaussCutPlane_isOpen.mem_nhds hz)
    have hzslit := gaussCutPlane_subset_gaussSlitPlane hz
    have hGAt  := (hGanalytic z hzslit).differentiableAt
    have hprod := hPAt.hasDerivAt.mul hGAt.hasDerivAt
    change deriv (P * G) z = P₁ z * G z + P z * deriv G z
    rw [hprod.deriv, hP₁eq hz]

  have hF₂eq  :=
    hF₁eq.deriv gaussCutPlane_isOpen
  intro z hz
  have hz0  := (gaussCutPlane_subset_regularPlane hz).1
  have hzslit := gaussCutPlane_subset_gaussSlitPlane hz
  have hPAt := (hPdiff z hz).differentiableAt (gaussCutPlane_isOpen.mem_nhds hz)
  have hP₁At := (hP₁diff z hz).differentiableAt (gaussCutPlane_isOpen.mem_nhds hz)
  have hGAt := (hGanalytic z hzslit).differentiableAt
  have hG₁At := (hGanalytic₁ z hzslit).differentiableAt
  have hsumDeriv : deriv (fun w => P₁ w * G w + P w * deriv G w) z =
      P₂ z * G z + P₁ z * deriv G z + P₁ z * deriv G z + P z * deriv (deriv G) z := by
    have hleft := hP₁At.hasDerivAt.mul hGAt.hasDerivAt
    have hright := hPAt.hasDerivAt.mul hG₁At.hasDerivAt
    have hsum := hleft.add hright
    have hleft' := hsum.deriv
    rw [hP₂eq hz, hP₁eq hz] at hleft'
    have hfun : (fun w => P₁ w * G w + P w * deriv G w) =
        P * deriv G + P₁ * G := by
      funext w
      change P₁ w * G w + P w * deriv G w =
        P w * deriv G w + P₁ w * G w
      ring
    grind
  have hpow₁ : z ^ (δ - 1) = z ^ δ / z := by
    simpa using Complex.cpow_sub δ 1 hz0
  have hpow₂ : z ^ (δ - 2) = z ^ δ / z ^ 2 := by
    simpa [Complex.cpow_two] using Complex.cpow_sub δ 2 hz0
  have hP₁val : P₁ z = δ * P z / z := by
    simp only [P₁, P]
    rw [hpow₁]
    ring
  have hP₂val : P₂ z = δ * (δ - 1) * P z / z ^ 2 := by
    grind
  have hFval : F z = P z * G z := by
    simp [F, gaussFPlus, P, G, δ, A, B, C]
  have hEqOp : gaussHolomorphicOperator a b c F z =
      P z * gaussHolomorphicOperator A B C G z := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator, hF₂eq hz]
    change z * (1 - z) * deriv (fun w => P₁ w * G w + P w * deriv G w) z +
      (c - (a + b + 1) * z) * deriv F z - a * b * F z =
      P z * (z * (1 - z) * deriv (deriv G) z +
        (C - (A + B + 1) * z) * deriv G z - A * B * G z)
    rw [hsumDeriv, hF₁eq hz, hFval, hP₁val, hP₂val]
    grind
  rw [hEqOp]
  simp [hsource z hz, G, A, B, C]

include H hH a b c in
/-- The powered second local solution at one solves the Gauss equation by reflection. -/
theorem gaussGPlus_holomorphicOperator_eq_zero
     (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c (gaussGPlus H a b c) z = 0 := by
  let c₀  := 1 + a + b - c
  let A  := a - c₀ + 1
  let B  := b - c₀ + 1
  let C  := 2 - c₀
  let P : ℂ → ℂ := fun z => z ^ (1 - c₀)

  let g  := gaussFPlus H a b c₀
  let f  := gaussGPlus H a b c
  have hc₀ : ∀ n : ℤ, c₀ ≠ (n : ℂ) := by
    intro n heq
    have hshift : c - a - b = (1 - n : ℤ) := by
      grind
    exact hδ (1 - n) hshift
  have hCfree : ∀ n : ℕ, C ≠ -(n : ℂ) := two_sub_parameter_ne_nat_neg hc₀
  have hchar := hH A B C hCfree
  have hGanalytic  := (hchar.1.analyticOnNhd gaussSlitPlane_isOpen_for_basis).mono
      gaussCutPlane_subset_gaussSlitPlane
  have hPanalytic : AnalyticOnNhd ℂ P gaussCutPlane := analyticOnNhd_id.cpow analyticOnNhd_const
      (fun z hz => gaussCutPlane_subset_Complex_slitPlane hz)
  have hganalytic : AnalyticOnNhd ℂ g gaussCutPlane := hPanalytic.mul hGanalytic
  have hganalytic₁  := hganalytic.deriv
  have hmap (z : ℂ) : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := (hasDerivAt_id z).const_sub (1 : ℂ)
  have hident : f = (fun z => g (1 - z)) := by
    funext z
    change (1 - z) ^ (c - a - b) * H (c - b) (c - a) (1 + c - a - b) (1 - z) =
      (1 - z) ^ (1 - c₀) * H (a - c₀ + 1) (b - c₀ + 1) (2 - c₀) (1 - z)
    grind
  have hderivEq : gaussCutPlane.EqOn (deriv f) (fun z => -deriv g (1 - z)) := by
    intro z hz
    have hw  := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hcomp := (hganalytic (1 - z) hw).differentiableAt.hasDerivAt.comp z (hmap z)
    calc
      deriv f z = deriv (fun w => g (1 - w)) z := by rw [hident]
      _ = -deriv g (1 - z) := by
        simpa [Function.comp_def, mul_comm] using hcomp.deriv
  have hderiv₂Eq : gaussCutPlane.EqOn (deriv (deriv f))
      (fun z => deriv (deriv g) (1 - z)) := by
    intro z hz
    have hfirst := hderivEq.deriv gaussCutPlane_isOpen hz
    have hw  := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hcomp := (hganalytic₁ (1 - z) hw).differentiableAt.hasDerivAt.comp z (hmap z)
    have hneg := hcomp.neg
    calc
      deriv (deriv f) z = deriv (fun w => -deriv g (1 - w)) z := hfirst
      _ = deriv (deriv g) (1 - z) := by
        simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hneg.deriv
  have hsource := gaussFPlus_holomorphicOperator_eq_zero hH a b c₀ hc₀
  intro z hz
  let w := 1 - z
  have hw : w ∈ gaussCutPlane := one_sub_gaussCutPlane_subset_gaussCutPlane hz
  have hEqOp : gaussHolomorphicOperator a b c f z =
      gaussHolomorphicOperator a b c₀ g w := by
    rw [gaussHolomorphicOperator, gaussHolomorphicOperator,
      hderiv₂Eq hz, hderivEq hz, hident]
    dsimp [w, c₀]
    ring
  rw [hEqOp]
  exact hsource w hw

end DOZZ.Proofs
