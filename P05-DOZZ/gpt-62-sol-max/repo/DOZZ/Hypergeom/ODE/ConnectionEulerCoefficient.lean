/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerFamilyLimits
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients
public import DOZZ.Hypergeom.ODE.ConnectionEulerBoxes

/-! Evaluation of the first zero-basis connection coefficient from the real Euler integral. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
include hH

/-- On the real Euler region, the first midpoint Cramer coefficient is the first Gamma
coefficient. Nonintegrality is retained only for the ODE connection-basis hypotheses. -/
theorem connectionMinusFirstCramer_eq_gamma_of_real
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < c - a - b)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionMinusFirstCramerCoefficient H (a, b, c) =
      gaussConnectionMinusGammaCoefficient₁ (a, b, c) := by
  exact connectionMinusFirstCramer_eq_of_endpoint_limit hH
    (gaussConnection_real_parameters hcInt hδInt) (by simpa using hδ)
    (gaussEuler_tendsto_firstGamma hH a b c ha hb hδ)

/-- The unpowered first Euler coefficient identity extends to a complex box. -/
theorem connectionMinusFirstCramer_eq_gamma_on_open_box :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
        ∀ a ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
          connectionMinusFirstCramerCoefficient H
              (gaussConnectionCoordinates c δ a) =
            gaussConnectionMinusGammaCoefficient₁ (gaussConnectionCoordinates c δ a) := by
  exact gaussConnection_eq_on_EulerBox1
    (fun _ hp => connectionMinusFirstCramerCoefficient_differentiableAt hH hp)
    (fun _ hp => gaussConnectionMinusGammaCoefficient₁_differentiableAt hp)
    (fun a b c ha hb _ _ hδ => connectionMinusFirstCramer_eq_gamma_of_real hH a b c ha hb hδ)

end

end DOZZ.Proofs
