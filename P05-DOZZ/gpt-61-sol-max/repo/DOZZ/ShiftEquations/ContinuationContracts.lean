/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.ReflectionBarR
public import DOZZ.Statements.Brownian.ReflectionExponent
public import DOZZ.Statements.Defs.ShiftCoeffA
public import DOZZ.Statements.FourPoint.DualCrossingL
public import DOZZ.Statements.FourPoint.GammaHalfUnitCrossingMultiplier
public import DOZZ.Statements.Correlations.BridgeMultiplicity
public import DOZZ.Statements.ShiftEquations.RbarCoefficient

public import DOZZ.Statements.Defs.DozzFormula
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant

/-! Exact shared outcomes of the continuation and gluing reductions. -/
@[expose] public section
open MeasureTheory Filter Topology Set
namespace DOZZ.Proofs.Contract
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)

/-- Shared fixedChargeShiftGluing proposition. -/
abbrev fixedChargeShiftGluing (γ μ η α₂ α₃ : ℝ) : Prop :=
  ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ, C z = R z * C (2 * Q γ - z)) ∧
              (∀ᶠ z in codiscrete ℂ,
                R (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
                  -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
                    C (z - γ / 2))

/-- Shared dualReflectionContinuation proposition. -/
abbrev dualReflectionContinuation (γ μ : ℝ) : Prop :=
  ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∃ cγ : ℂ, cγ ≠ 0 ∧
                cγ = ((γ : ℂ) ^ 2 / 4) * (μ * Real.pi : ℂ) * R γ ∧
                ∀ᶠ z in codiscrete ℂ,
                  R z = -cγ * R (z + 2 / γ) /
                    (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) *
                      lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ))

/-- Shared residualUnitVolume proposition. -/
abbrev residualUnitVolume (γ μ η : ℝ) (U : ℂ → ℂ) : Prop :=
  ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ cγ : ℂ, cγ = 1 ∧
              ∀ α₁ α₂ α₃ : ℝ,
                Q γ - η < α₁ → α₁ < Q γ →
                Q γ - η < α₂ → α₂ < Q γ →
                Q γ - η < α₃ → α₃ < Q γ →
                  (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) =
                    cγ * ((μ : ℂ) ^ ((sExp γ α₁ α₂ α₃ : ℂ)) /
                      Complex.Gamma (sExp γ α₁ α₂ α₃ : ℂ) *
                        dozzFormula γ μ U (α₁ : ℂ) (α₂ : ℂ) (α₃ : ℂ))

/-- Shared singleChargeContinuation proposition. -/
abbrev singleChargeContinuation (γ μ η α₂ α₃ : ℝ) : Prop :=
  ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ,
        MeromorphicOn C {z | |z.im| < h} ∧
        (∀ α : ℝ, 2 * η < α → α < Q γ →
          C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
        ∀ᶠ z in codiscrete ℂ,
          C (z + γ / 2) =
            -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
              C (z - γ / 2)

end DOZZ.Proofs.Contract
