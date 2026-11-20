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
  have hp : (a, b, c) ∈ gaussConnectionParameterDomain := by
    change (∀ n : ℤ, c ≠ (n : ℂ)) ∧ ∀ n : ℤ, c - a - b ≠ (n : ℂ)
    exact ⟨hc, hδ⟩
  exact gauss_connection_minus_of_box_coefficients hH gaussConnection_firstBox gaussConnection_secondBox
    (connectionMinusFirstCramer_eq_gamma_on_open_box hH)
    ((gaussConnection_eq_on_EulerBox2
      (fun _ hp => connectionMinusSecondCramerCoefficient_differentiableAt hH hp)
      (fun _ hp => gaussConnectionMinusGammaCoefficient₂_differentiableAt hp)
      (fun a b c ha hb hca hcb _ _ _ _ hδ => connectionMinusSecondCramer_eq_gamma_of_real hH a b c ha hb hca hcb hδ))) hp

end DOZZ.Proofs
