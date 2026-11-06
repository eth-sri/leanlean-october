/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
public import DOZZ.Hypergeom.ODE.ConnectionEulerContinuation
public import DOZZ.Hypergeom.ODE.ConnectionEulerPlusCoefficient

/-! Proof of `DOZZ.gauss_connection_plus`, the powered zero-basis Gauss connection formula. -/

public section

namespace DOZZ.Proofs

/-- The powered Gauss connection formula follows directly by continuation from the two real Euler regions. -/
theorem gauss_connection_plus {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussFPlus H a b c z =
        (Complex.Gamma (2 - c) * Complex.Gamma (c - a - b) *
          (Complex.Gamma (1 - a))⁻¹ * (Complex.Gamma (1 - b))⁻¹) *
            gaussGMinus H a b c z +
        (Complex.Gamma (2 - c) * Complex.Gamma (a + b - c) *
          (Complex.Gamma (a - c + 1))⁻¹ * (Complex.Gamma (b - c + 1))⁻¹) *
            gaussGPlus H a b c z := by
  have hp : (a, b, c) ∈ gaussConnectionParameterDomain := ⟨hc, hδ⟩
  have hfirst := gaussConnection_eq_of_positiveEuler
    (fun p hp => connectionPlusFirstCramerCoefficient_differentiableAt hH hp)
    (fun p hp => gaussConnectionPlusGammaCoefficient₁_differentiableAt hp)
    (fun a b c ha hb hd hc1 hci hdi =>
      connectionPlusFirstCramer_eq_gamma_of_real hH a b c
        (by linarith) (by linarith) hd hci hdi) hp
  have hsecond := gaussConnection_eq_of_negativeEuler
    (fun p hp => connectionPlusSecondCramerCoefficient_differentiableAt hH hp)
    (fun p hp => gaussConnectionPlusGammaCoefficient₂_differentiableAt hp)
    (fun a b c ha hb hca hcb hd hc1 hci hdi =>
      connectionPlusSecondCramer_eq_gamma_of_real hH a b c
        (by linarith) (by linarith) (by linarith) (by linarith) hd hci hdi) hp
  intro z hz
  rw [gaussFPlus_eq_connectionMidpointCramer hH hp z hz, hfirst, hsecond]
  abel

end DOZZ.Proofs
