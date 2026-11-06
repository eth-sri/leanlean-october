/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionAnalyticContinuation
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! The Euler-box coefficient evaluations imply the global connection formulas. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A nonempty product neighborhood in `(c, δ, a)` coordinates inside the connection domain. -/
structure GaussConnectionOpenBox where
  S : Set ℂ
  T : Set ℂ
  V : Set ℂ
  c₀ : ℂ
  δ₀ : ℂ
  a₀ : ℂ
  hSopen : IsOpen S
  hTopen : IsOpen T
  hVopen : IsOpen V
  hc₀ : c₀ ∈ S
  hδ₀ : δ₀ ∈ T
  ha₀ : a₀ ∈ V
  hS : S ⊆ gaussConnectionIntegerRangeᶜ
  hT : T ⊆ gaussConnectionIntegerRangeᶜ
section
variable {H : ℂ → ℂ → ℂ → ℂ → ℂ}
section
variable (hH : IsGaussHypergeometricFamily H) (firstBox secondBox : GaussConnectionOpenBox)
include hH

/-- If the two midpoint Cramer coefficients agree with their Gamma values on possibly different
nonempty open Euler boxes, successive one-variable continuation gives the zero-basis connection
formula `DOZZ.gauss_connection_minus`. Separate boxes are necessary: the two endpoint coefficient
evaluations use disjoint exponent-sign regions. -/
theorem gauss_connection_minus_of_box_coefficients
    (hfirst : ∀ c ∈ firstBox.S, ∀ δ ∈ firstBox.T, ∀ a ∈ firstBox.V,
      connectionMinusFirstCramerCoefficient H (gaussConnectionCoordinates c δ a) =
        gaussConnectionMinusGammaCoefficient₁ (gaussConnectionCoordinates c δ a))
    (hsecond : ∀ c ∈ secondBox.S, ∀ δ ∈ secondBox.T, ∀ a ∈ secondBox.V,
      connectionMinusSecondCramerCoefficient H (gaussConnectionCoordinates c δ a) =
        gaussConnectionMinusGammaCoefficient₂ (gaussConnectionCoordinates c δ a))
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    ∀ z ∈ gaussCutPlane,
      gaussFMinus H p.1 p.2.1 p.2.2 z =
        (Complex.Gamma p.2.2 * Complex.Gamma (p.2.2 - p.1 - p.2.1) *
          (Complex.Gamma (p.2.2 - p.1))⁻¹ * (Complex.Gamma (p.2.2 - p.2.1))⁻¹) *
            gaussGMinus H p.1 p.2.1 p.2.2 z +
        (Complex.Gamma p.2.2 * Complex.Gamma (p.1 + p.2.1 - p.2.2) *
          (Complex.Gamma p.1)⁻¹ * (Complex.Gamma p.2.1)⁻¹) *
            gaussGPlus H p.1 p.2.1 p.2.2 z := by
  let firstCramer := connectionMinusFirstCramerCoefficient H
  let firstGamma := gaussConnectionMinusGammaCoefficient₁
  let secondCramer := connectionMinusSecondCramerCoefficient H
  let secondGamma := gaussConnectionMinusGammaCoefficient₂
  have hfirstGlobal : firstCramer p = firstGamma p := eq_of_eq_on_open_gaussConnection_box
     
      (hf := fun q hq => connectionMinusFirstCramerCoefficient_differentiableAt hH hq)
      (hg := fun q hq => gaussConnectionMinusGammaCoefficient₁_differentiableAt hq)
      firstBox.hSopen firstBox.hTopen firstBox.hVopen
      firstBox.hc₀ firstBox.hδ₀ firstBox.ha₀ firstBox.hS firstBox.hT
      (by assumption) hp
  have hsecondGlobal : secondCramer p = secondGamma p := eq_of_eq_on_open_gaussConnection_box
     
      (hf := fun q hq => connectionMinusSecondCramerCoefficient_differentiableAt hH hq)
      (hg := fun q hq => gaussConnectionMinusGammaCoefficient₂_differentiableAt hq)
      secondBox.hSopen secondBox.hTopen secondBox.hVopen
      secondBox.hc₀ secondBox.hδ₀ secondBox.ha₀ secondBox.hS secondBox.hT
      (by assumption) hp
  change connectionMinusFirstCramerCoefficient H p =
    gaussConnectionMinusGammaCoefficient₁ p at hfirstGlobal
  change connectionMinusSecondCramerCoefficient H p =
    gaussConnectionMinusGammaCoefficient₂ p at hsecondGlobal
  intro z hz
  rw [(gaussFMinus_eq_connectionMidpointCramer hH hp) z hz, hfirstGlobal, hsecondGlobal]
  rfl

/-- If the two midpoint Cramer coefficients for the powered zero-basis solution agree with their
Gamma values on possibly different nonempty open Euler boxes, continuation gives the powered
connection formula `DOZZ.gauss_connection_plus`. -/
theorem gauss_connection_plus_of_box_coefficients
    (hfirst : ∀ c ∈ firstBox.S, ∀ δ ∈ firstBox.T, ∀ a ∈ firstBox.V,
      connectionPlusFirstCramerCoefficient H (gaussConnectionCoordinates c δ a) =
        gaussConnectionPlusGammaCoefficient₁ (gaussConnectionCoordinates c δ a))
    (hsecond : ∀ c ∈ secondBox.S, ∀ δ ∈ secondBox.T, ∀ a ∈ secondBox.V,
      connectionPlusSecondCramerCoefficient H (gaussConnectionCoordinates c δ a) =
        gaussConnectionPlusGammaCoefficient₂ (gaussConnectionCoordinates c δ a))
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    ∀ z ∈ gaussCutPlane,
      gaussFPlus H p.1 p.2.1 p.2.2 z =
        (Complex.Gamma (2 - p.2.2) * Complex.Gamma (p.2.2 - p.1 - p.2.1) *
          (Complex.Gamma (1 - p.1))⁻¹ * (Complex.Gamma (1 - p.2.1))⁻¹) *
            gaussGMinus H p.1 p.2.1 p.2.2 z +
        (Complex.Gamma (2 - p.2.2) * Complex.Gamma (p.1 + p.2.1 - p.2.2) *
          (Complex.Gamma (p.1 - p.2.2 + 1))⁻¹ *
            (Complex.Gamma (p.2.1 - p.2.2 + 1))⁻¹) *
            gaussGPlus H p.1 p.2.1 p.2.2 z := by
  let firstCramer := connectionPlusFirstCramerCoefficient H
  let firstGamma := gaussConnectionPlusGammaCoefficient₁
  let secondCramer := connectionPlusSecondCramerCoefficient H
  let secondGamma := gaussConnectionPlusGammaCoefficient₂
  have hfirstGlobal : firstCramer p = firstGamma p := eq_of_eq_on_open_gaussConnection_box
      (f := firstCramer) (g := firstGamma)
      (hf := fun q hq => connectionPlusFirstCramerCoefficient_differentiableAt hH hq)
      (hg := fun q hq => gaussConnectionPlusGammaCoefficient₁_differentiableAt hq)
      firstBox.hSopen firstBox.hTopen firstBox.hVopen
      firstBox.hc₀ firstBox.hδ₀ firstBox.ha₀ firstBox.hS firstBox.hT
      (by assumption) hp
  have hsecondGlobal : secondCramer p = secondGamma p := eq_of_eq_on_open_gaussConnection_box
      (f := secondCramer) (g := secondGamma)
      (hf := fun q hq => connectionPlusSecondCramerCoefficient_differentiableAt hH hq)
      (hg := fun q hq => gaussConnectionPlusGammaCoefficient₂_differentiableAt hq)
      secondBox.hSopen secondBox.hTopen secondBox.hVopen
      secondBox.hc₀ secondBox.hδ₀ secondBox.ha₀ secondBox.hS secondBox.hT
      (by assumption) hp
  change connectionPlusFirstCramerCoefficient H p =
    gaussConnectionPlusGammaCoefficient₁ p at hfirstGlobal
  change connectionPlusSecondCramerCoefficient H p =
    gaussConnectionPlusGammaCoefficient₂ p at hsecondGlobal
  intro z hz
  rw [(gaussFPlus_eq_connectionMidpointCramer hH hp) z hz, hfirstGlobal, hsecondGlobal]
  simp [gaussConnectionPlusGammaCoefficient₁, gaussConnectionPlusGammaCoefficient₂]

end

end

end DOZZ.Proofs
