/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
public import DOZZ.Hypergeom.ODE.ConnectionEulerContinuation
public import DOZZ.Hypergeom.ODE.ConnectionEulerCoefficient
public import DOZZ.Hypergeom.ODE.ConnectionEulerSecondCoefficient

/-! Proof of `DOZZ.gauss_connection_minus`, the zero-basis Gauss connection formula. -/

public section

namespace DOZZ.Proofs

/-- The zero-basis Gauss connection formula follows directly by continuation from the two real Euler regions. -/
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
  have hp : (a, b, c) ∈ gaussConnectionParameterDomain := ⟨hc, hδ⟩
  have hfirst := gaussConnection_eq_of_positiveEuler
    (fun p hp => connectionMinusFirstCramerCoefficient_differentiableAt hH hp)
    (fun p hp => gaussConnectionMinusGammaCoefficient₁_differentiableAt hp)
    (fun a b c ha hb hd _ hci hdi =>
      connectionMinusFirstCramer_eq_gamma_of_real hH a b c ha hb hd hci hdi) hp
  have hsecond := gaussConnection_eq_of_negativeEuler
    (fun p hp => connectionMinusSecondCramerCoefficient_differentiableAt hH hp)
    (fun p hp => gaussConnectionMinusGammaCoefficient₂_differentiableAt hp)
    (fun a b c ha hb hca hcb hd _ hci hdi =>
      connectionMinusSecondCramer_eq_gamma_of_real hH a b c ha hb hca hcb hd hci hdi) hp
  intro z hz
  rw [gaussFMinus_eq_connectionMidpointCramer hH hp z hz, hfirst, hsecond]
  abel

end DOZZ.Proofs
