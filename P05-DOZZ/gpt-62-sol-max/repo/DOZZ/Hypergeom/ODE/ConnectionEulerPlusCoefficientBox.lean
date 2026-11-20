/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionEulerPlusCoefficient
public import DOZZ.Hypergeom.ODE.ConnectionEulerSecondCoefficientBox

/-! Holomorphic continuation of both powered connection coefficients from real Euler boxes. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
include hH

/-- The powered first Euler coefficient identity extends to a complex box. -/
theorem connectionPlusFirstCramer_eq_gamma_on_open_box :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
        ∀ a ∈ Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ),
          connectionPlusFirstCramerCoefficient H
              (gaussConnectionCoordinates c δ a) =
            gaussConnectionPlusGammaCoefficient₁ (gaussConnectionCoordinates c δ a) := by
  exact gaussConnection_eq_on_EulerBox1
    (fun _ hp => connectionPlusFirstCramerCoefficient_differentiableAt hH hp)
    (fun _ hp => gaussConnectionPlusGammaCoefficient₁_differentiableAt hp)
    (fun a b c _ _ hA hB hδ => connectionPlusFirstCramer_eq_gamma_of_real hH a b c hA hB hδ)

/-- The powered second Euler coefficient identity extends to a complex box. -/
theorem connectionPlusSecondCramer_eq_gamma_on_open_box :
    ∀ c ∈ Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ),
      ∀ δ ∈ Metric.ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ),
        ∀ a ∈ Metric.ball (1 / 2 : ℂ) (1 / 16 : ℝ),
          connectionPlusSecondCramerCoefficient H
              (gaussConnectionCoordinates c δ a) =
            gaussConnectionPlusGammaCoefficient₂ (gaussConnectionCoordinates c δ a) := by
  exact gaussConnection_eq_on_EulerBox2
    (fun _ hp => connectionPlusSecondCramerCoefficient_differentiableAt hH hp)
    (fun _ hp => gaussConnectionPlusGammaCoefficient₂_differentiableAt hp)
    (fun a b c _ _ _ _ hA hB h1a h1b hδ => connectionPlusSecondCramer_eq_gamma_of_real hH a b c hA hB h1a h1b hδ)

end

end DOZZ.Proofs
