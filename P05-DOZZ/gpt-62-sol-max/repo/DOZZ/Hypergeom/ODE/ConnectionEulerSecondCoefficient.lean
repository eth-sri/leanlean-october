/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerFamilyLimits
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! Evaluation of the second zero-basis connection coefficient from Euler's transformation. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

/-- On the negative-excess real Euler region, the second midpoint Cramer coefficient is the
second Gamma coefficient. Euler's transformation converts the endpoint into a positive-excess
Euler integral, where dominated convergence applies. -/
theorem connectionMinusSecondCramer_eq_gamma_of_real
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hca : 0 < c - a) (hcb : 0 < c - b) (hδ : c - a - b < 0)
    (hcInt : (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hδInt : ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ) :
    connectionMinusSecondCramerCoefficient H (a, b, c) =
      gaussConnectionMinusGammaCoefficient₂ (a, b, c) := by
  exact connectionMinusSecondCramer_eq_of_scaled_endpoint_limit hH
    (gaussConnection_real_parameters hcInt hδInt) (by simp; linarith)
    (gaussEuler_tendsto_secondGamma hH a b c ha hb hca hcb hδ)

end DOZZ.Proofs
