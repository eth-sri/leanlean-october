/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
public import DOZZ.Hypergeom.ConnectionFormulaFromBox
public import DOZZ.Hypergeom.ODE.ConnectionEulerCoefficient
public import DOZZ.Hypergeom.ODE.ConnectionEulerSecondCoefficientBox

/-! Proof of `DOZZ.gauss_connection_minus`, the zero-basis Gauss connection formula. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The zero-basis Gauss connection formula follows from the two Euler coefficient boxes. -/
theorem gauss_connection_minus {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussFMinus H a b c z =
        (Complex.Gamma c * Complex.Gamma (c - a - b) *
          (Complex.Gamma (c - a))⁻¹ * (Complex.Gamma (c - b))⁻¹) *
            gaussGMinus H a b c z +
        (Complex.Gamma c * Complex.Gamma (a + b - c) *
          (Complex.Gamma a)⁻¹ * (Complex.Gamma b)⁻¹) * gaussGPlus H a b c z := by
  let firstBox : GaussConnectionOpenBox := {
    S := Metric.ball (3 / 4) (1 / 8)
    T := Metric.ball (1 / 4) (1 / 8)
    V := Metric.ball (1 / 4) (1 / 8)
    c₀ := 3 / 4
    δ₀ := 1 / 4
    a₀ := 1 / 4
    hSopen := Metric.isOpen_ball
    hTopen := Metric.isOpen_ball
    hVopen := Metric.isOpen_ball
    hc₀ := by simp
    hδ₀ := by simp
    ha₀ := by simp
    hS := by
      simpa [Complex.ofReal_div] using
        (DOZZ.Proofs.ofReal_ball_subset_integerRange_compl
          (3 / 4) (1 / 8) (by norm_num) (by norm_num) (by norm_num))
    hT := by
      simpa [Complex.ofReal_div] using
        (DOZZ.Proofs.ofReal_ball_subset_integerRange_compl
          (1 / 4) (1 / 8) (by norm_num) (by norm_num) (by norm_num))
  }
  let secondBox : GaussConnectionOpenBox := {
    S := Metric.ball (3 / 4) (1 / 8)
    T := Metric.ball (-(1 / 4)) (1 / 16)
    V := Metric.ball (1 / 2) (1 / 16)
    c₀ := 3 / 4
    δ₀ := -(1 / 4)
    a₀ := 1 / 2
    hSopen := Metric.isOpen_ball
    hTopen := Metric.isOpen_ball
    hVopen := Metric.isOpen_ball
    hc₀ := by simp
    hδ₀ := by simp
    ha₀ := by simp
    hS := by
      simpa [Complex.ofReal_div] using
        (DOZZ.Proofs.ofReal_ball_subset_integerRange_compl
          (3 / 4) (1 / 8) (by norm_num) (by norm_num) (by norm_num))
    hT := secondCoefficient_negativeQuarter_ball_avoids_integers
  }
  have hp : (a, b, c) ∈ gaussConnectionParameterDomain := by
    tauto
  exact gauss_connection_minus_of_box_coefficients hH firstBox secondBox
    (connectionMinusFirstCramer_eq_gamma_on_open_box hH)
    (connectionMinusSecondCramer_eq_gamma_on_open_box hH) hp

end DOZZ.Proofs
