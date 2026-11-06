/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Contracts
public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
public import DOZZ.Statements.Hypergeom.PlanarGaussConstant

/-! Shared physical Gauss-expansion contracts for the crossing and shift arguments. -/
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs.Contract
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
  (γ μ α₁ α₂ α₃ : ℝ) (H : ℂ → ℂ → ℂ → ℂ → ℂ)

abbrev gammaHalfUnreflected : Prop :=
  let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
      let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
      let c := gaussParameterC γ (γ / 2) α₁
      ∀ z ∈ gaussCutPlane,
        fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
              ‖gaussFMinus H a b c z‖ ^ 2 +
            (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
              structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
                ‖gaussFPlus H a b c z‖ ^ 2

abbrev gammaHalfReflected (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) : Prop :=
  let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
        let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
        let c := gaussParameterC γ (γ / 2) α₁
        ∀ z ∈ gaussCutPlane,
          fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
            structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
                ‖gaussFMinus H a b c z‖ ^ 2 +
              reflectionR P γ μ α₁ B Z *
                structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ *
                  ‖gaussFPlus H a b c z‖ ^ 2

abbrev gaussDiagonal (χ : ℝ) : Prop :=
  let a := gaussParameterA γ χ α₁ α₂ α₃
    let b := gaussParameterB γ χ α₁ α₂ α₃
    let c := gaussParameterC γ χ α₁
    ∀ z ∈ gaussCutPlane,
      fourPointT P M γ μ (-χ) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - χ) α₂ α₃ *
          (‖gaussFMinus H a b c z‖ ^ 2 +
            gaussCoefficientRatio a b c *
              ‖gaussFPlus H a b c z‖ ^ 2)

end DOZZ.Proofs.Contract
