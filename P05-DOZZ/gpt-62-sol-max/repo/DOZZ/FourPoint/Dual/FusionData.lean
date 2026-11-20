/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.FourPoint.FourPointT
public import DOZZ.Statements.Hypergeom.GaussParameterA
public import DOZZ.Statements.Hypergeom.GaussParameterB
public import DOZZ.Statements.Hypergeom.GaussParameterC
public import DOZZ.Statements.Hypergeom.GaussFPlus
public import DOZZ.Statements.Hypergeom.GaussFMinus
public import DOZZ.Statements.Hypergeom.GaussCutPlane
public import DOZZ.Statements.Hypergeom.IsGaussHypergeometricFamily

@[expose] public section

open MeasureTheory Filter

namespace DOZZ

/-- The dual fusion expansion at zero and its exact hypergeometric representation. -/
abbrev DualFusionData {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (X : Ω → Distr) (H : ℂ → ℂ → ℂ → ℂ → ℂ) (γ μ α₁ α₂ α₃ : ℝ) : Prop :=
  ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
    ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
      IsReflectionData P γ α₁ (B α₁) Z ∧
      let a := gaussParameterA γ (2 / γ) α₁ α₂ α₃
      let b := gaussParameterB γ (2 / γ) α₁ α₂ α₃
      let c := gaussParameterC γ (2 / γ) α₁
      let κ := (4 / γ) * (Q γ - α₁)
      (∃ r : ℂ → ℝ,
        (∀ z, fourPointT P M γ μ (-2 / γ) α₁ α₂ α₃ z =
          structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ +
            reflectionR P γ μ α₁ (B α₁) Z *
              structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ *
                (‖z‖ ^ κ : ℝ) + r z) ∧
          Tendsto (fun z => r z / ‖z‖ ^ κ)
            (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0)) ∧
        (∀ z ∈ gaussCutPlane,
          fourPointT P M γ μ (-2 / γ) α₁ α₂ α₃ z =
            structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
                ‖gaussFMinus H a b c z‖ ^ 2 +
              reflectionR P γ μ α₁ (B α₁) Z *
                structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ *
                  ‖gaussFPlus H a b c z‖ ^ 2)

end DOZZ
