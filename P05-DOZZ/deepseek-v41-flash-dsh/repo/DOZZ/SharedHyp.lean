/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Order.Notation
public import Mathlib.Basic.Real.Basic
public import DOZZ.Statements.Defs.Q
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.NNReal.Defs
public import DOZZ.Statements.Hypergeom.IsGaussHypergeometricFamily
public import DOZZ.Statements.Defs.Distr
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Brownian.BrownianPath
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Hypergeom.GaussParameterA
public import DOZZ.Statements.Hypergeom.GaussParameterB
public import DOZZ.Statements.Hypergeom.GaussParameterC
public import DOZZ.Statements.FourPoint.FourPointT
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Hypergeom.GaussCutPlane
public import DOZZ.Statements.Hypergeom.GaussFMinus
public import DOZZ.Statements.Hypergeom.GaussFPlus
public import DOZZ.Statements.FourPoint.DualCrossingL
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.FourPoint.GammaHalfUnitCrossingMultiplier
public import Mathlib.Analysis.Meromorphic.Basic
public import DOZZ.Statements.Defs.LFun
public import DOZZ.Statements.Defs.ShiftCoeffA
public import DOZZ.Statements.Correlations.UniformPositiveC1Family
public import DOZZ.Statements.Correlations.LocalSingularMass
public import DOZZ.Statements.Correlations.OneInsertionTailCoefficient
public import DOZZ.Statements.Brownian.ReflectionExponent
public import DOZZ.Statements.Correlations.TwoInsertionTailCeiling
public import DOZZ.Statements.Correlations.OneInsertionErrorCeiling
public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import Mathlib
import DOZZ.Statements.FourPoint.FourPointT
import DOZZ.Statements.Hypergeom.GaussFMinus
import DOZZ.Statements.FourPoint.DualCrossingL
import DOZZ.Statements.FourPoint.DualCrossingMultiplier
import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Statements.Defs.LFun
import DOZZ.Statements.Defs.ShiftCoeffA
import DOZZ.Statements.Correlations.LocalSingularMass
import DOZZ.Statements.Correlations.OneInsertionTailCoefficient
import DOZZ.Statements.Correlations.UniformPositiveC1Family
import DOZZ.Statements.Correlations.TwoInsertionTailCeiling
import DOZZ.Statements.Brownian.ReflectionBarR
import DOZZ.Statements.Hypergeom.GaussParameterA
import DOZZ.Statements.Hypergeom.GaussParameterB
import DOZZ.Statements.Hypergeom.GaussParameterC
import DOZZ.Statements.Defs.Q
import DOZZ.Statements.Defs.IsEquatorGFF
import DOZZ.Statements.Defs.IsGMCOf
import DOZZ.Statements.Brownian.IsSourceLateralProjection
import DOZZ.Statements.Brownian.IsReflectionData
import DOZZ.Statements.Brownian.BrownianPath
import DOZZ.Statements.Hypergeom.GaussCutPlane
import DOZZ.Statements.FourPoint.DualCrossingL
import DOZZ.Statements.FourPoint.DualCrossingMultiplier
import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Statements.Defs.LFun
import DOZZ.Statements.Defs.ShiftCoeffA
import DOZZ.Statements.Correlations.LocalSingularMass
import DOZZ.Statements.Correlations.OneInsertionTailCoefficient
import DOZZ.Statements.Correlations.UniformPositiveC1Family
import DOZZ.Statements.Correlations.TwoInsertionTailCeiling
import DOZZ.Statements.Brownian.ReflectionBarR

/-! Recurrent hypothesis bundles, shared across the Gaussian-field developments. -/

@[expose] public section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal

universe u

namespace DOZZ.Proofs

/-- Joint measurability of a circle-average field. -/
abbrev MeasurableCircleAvg {Ω : Type*} [MeasurableSpace Ω] (Xc : Ω → ℂ → ℝ → ℝ) : Prop :=
  Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2)

/-- Almost every realization of a circle-average field is continuous. -/
abbrev ContinuousCircleAvg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)

/-- `L²` membership of the field sections in a ball. -/
abbrev MemLpBall {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : Ω → ℂ → ℝ)
    (c : ℂ) (ρ : ℝ) : Prop :=
  ∀ z ∈ Metric.ball c ρ, MemLp (fun ω => V ω z) 2 P

/-- Vanishing mean of the field sections in a ball. -/
abbrev MeanZeroBall {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : Ω → ℂ → ℝ)
    (c : ℂ) (ρ : ℝ) : Prop :=
  ∀ z ∈ Metric.ball c ρ, (∫ ω, V ω z ∂P) = 0

/-- Finiteness of a random measure on compact sets avoiding the origin. -/
abbrev FiniteOffOrigin {Ω : Type*} (N : Ω → Measure ℂ) : Prop :=
  ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤


/-- The fusion hypothesis bundle for the degenerate four-point seed. -/
abbrev FusionHyp : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω]
      {H : ℂ → ℂ → ℂ → ℂ → ℂ}
      (_hH : IsGaussHypergeometricFamily H)
      (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
      (γ μ α₁ α₂ α₃ η ξ : ℝ)
      (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
      (_hη : 0 < η) (_hη₂ : η < γ / 2) (_hξ : 0 < ξ) (_hξ₂ : ξ < 1)
      (_hαlo : Q γ - η < α₁) (_hαhi : α₁ < Q γ)
      (_hα₂ : α₂ < Q γ) (_hα₃ : α₃ < Q γ)
      (_hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
      (_hslack₁ : (4 / γ) * (Q γ - α₁) < ξ)
      (_hslack₂ : (4 / γ) * (Q γ - α₁) <
        (1 - ξ) * (4 - γ * α₁ - 2 * γ * η))
      (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
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
              Filter.Tendsto (fun z => r z / ‖z‖ ^ κ)
                (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0)) ∧
            (∀ z ∈ gaussCutPlane,
              fourPointT P M γ μ (-2 / γ) α₁ α₂ α₃ z =
                structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
                    ‖gaussFMinus H a b c z‖ ^ 2 +
                  reflectionR P γ μ α₁ (B α₁) Z *
                    structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ *
                      ‖gaussFPlus H a b c z‖ ^ 2))

/-- The slack condition on the three charges. -/
abbrev SeibergSlack (γ α₁ α₂ α₃ : ℝ) : Prop :=
  2 * Q γ + γ / 2 < α₁ + α₂ + α₃

/-- A complex number is not a nonpositive integer. -/
abbrev NotNegPole (c : ℂ) : Prop := ∀ n : ℕ, c ≠ -(n : ℂ)

/-- The admissible drift window. -/
abbrev DriftWindow (γ η : ℝ) : Prop := 0 < η ∧ Q γ - 2 * η > γ

/-- A bounded nonnegative weight. -/
abbrev BoundedWeight {S : Type*} (h : S → ℝ≥0) : Prop := ∃ c : ℝ≥0, ∀ x : S, h x ≤ c

/-- The dual crossing seed hypothesis. -/
abbrev SeedHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ) : Prop :=
  ∀ α ε α' : ℝ, α < Q γ → ε < Q γ → α' < Q γ → 2 * Q γ + 2 / γ < α + ε + α' →
    ∃ Bε Bα : Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ ε Bε Z ∧
        IsReflectionData P γ α Bα Z ∧
        reflectionR P γ μ ε Bε Z * structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
          dualCrossingL γ ε α α' * reflectionR P γ μ α Bα Z *
            structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α'

/-- The unit-volume crossing hypothesis. -/
abbrev CrossingHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (γ : ℝ) : Prop :=
  ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
    2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α

/-- The first structure-shift hypothesis. -/
abbrev FirstShiftHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ) : Prop :=
  ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
    IsSourceLateralProjection P X γ M Z ∧
      (∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧
    ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ, MeromorphicOn R {z | |z.im| < h} ∧
      (∀ α : ℝ, γ / 2 < α → α < Q γ →
        R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) ∧
      ∀ᶠ z in codiscrete ℂ, R (z - γ / 2) = -(μ * Real.pi : ℂ) * R z /
        (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
          lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2))

/-- Shared hypothesis `hShiftGluing`. -/
abbrev ShiftGluingHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ : ℝ) (μ : ℝ) : Prop :=
  ∀ η : ℝ, (0 < η ∧ Q γ - 2 * η > γ) → ∀ α₂ α₃ : ℝ, (Q γ - η < α₂ ∧ α₂ < Q γ) → (Q γ - η < α₃ ∧ α₃ < Q γ) → ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ, IsSourceLateralProjection P X γ M Z ∧ (∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧ ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ, MeromorphicOn C {z | |z.im| < h} ∧ MeromorphicOn R {z | |z.im| < h} ∧ (∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧ (∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) ∧ (∀ᶠ z in codiscrete ℂ, C z = R z * C (2 * Q γ - z)) ∧ (∀ᶠ z in codiscrete ℂ, R (z + γ / 2) * C (2 * Q γ - z - γ / 2) = -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) * C (z - γ / 2))

/-- Shared hypothesis `hTail`. -/
abbrev TailHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ : ℝ) : Prop :=
  ∀ (K2 K3 : Set ℂ) (_ : IsCompact K2) (_ : IsCompact K3) (_ : ∀ z ∈ K2, 2 ≤ ‖z‖) (_ : ∀ z ∈ K3, 2 ≤ ‖z‖) (_ : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2 - z3‖) (A2 A3 : Set ℝ) (_ : IsCompact A2) (_ : IsCompact A3) (_ : ∀ α ∈ A2, γ / 2 < α ∧ α < Q γ) (_ : ∀ α ∈ A3, γ / 2 < α ∧ α < Q γ) (F2s F3s : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ) (_ : UniformPositiveC1Family K2 F2s radius supBound derivBound lowerBound) (_ : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound), ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ, IsSourceLateralProjection P X γ M Z ∧ (∀ α, (α ∈ A2 ∨ α ∈ A3) → IsReflectionData P γ α (B α) Z) ∧ ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧ ∀ z2 ∈ K2, ∀ z3 ∈ K3, ∀ α2 ∈ A2, ∀ α3 ∈ A3, ∀ F2 ∈ F2s z2, ∀ F3 ∈ F3s z3, ∀ x : ℝ, 1 ≤ x → |(P {ω | ENNReal.ofReal x < localSingularMass M F2 z2 γ α2 ω + localSingularMass M F3 z3 γ α3 ω}).toReal - (oneInsertionTailCoefficient γ α2 z2 (F2 z2) (reflectionBarR P γ α2 (B α2) Z) * Real.rpow x (-reflectionExponent γ α2) + oneInsertionTailCoefficient γ α3 z3 (F3 z3) (reflectionBarR P γ α3 (B α3) Z) * Real.rpow x (-reflectionExponent γ α3))| ≤ C * Real.rpow x (-(twoInsertionTailCeiling γ α2 α3 - θ))

/-- Shared hypothesis `hone`. -/
abbrev OneInsertionHyp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ : ℝ) : Prop :=
  ∀ (Kz : Set ℂ) (_hKz : IsCompact Kz) (_hz : ∀ z ∈ Kz, 2 ≤ ‖z‖) (Kα : Set ℝ) (_hKα : IsCompact Kα) (_hα : ∀ α ∈ Kα, γ / 2 < α ∧ α < Q γ) (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ) (_hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound), ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ, IsSourceLateralProjection P X γ M Z ∧ (∀ α ∈ Kα, IsReflectionData P γ α (B α) Z) ∧ ∀ η : ℝ, 0 < η → (∀ α ∈ Kα, η < oneInsertionErrorCeiling γ α) → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ F ∈ Family z, ∀ x : ℝ, 1 ≤ x → |(P {ω | ENNReal.ofReal x < localSingularMass M F z γ α ω}).toReal - oneInsertionTailCoefficient γ α z (F z) (reflectionBarR P γ α (B α) Z) * Real.rpow x (-reflectionExponent γ α)| ≤ C * Real.rpow x (-reflectionExponent γ α - η) 

/-- The covariance hypothesis for the Poisson family in a ball. -/
abbrev CovarianceBall {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (V : Ω → ℂ → ℝ)
    (c : ℂ) (ρ R : ℝ) : Prop :=
  ∀ z w, z ∈ Metric.ball c ρ → w ∈ Metric.ball c ρ →
    covariance (fun ω => V ω z) (fun ω => V ω w) P =
      Real.log R + Real.log ρ - Real.log ‖(ρ : ℂ) ^ 2 - (z - c) * star (w - c)‖

/-- The reflection data family hypothesis. -/
abbrev ReflectionDataFamily {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (BR : ℝ → Ω → BrownianPath × BrownianPath) (ZR : Ω → Measure ℝ) : Prop :=
  ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (BR α) ZR

/-- The reflection-coefficient family hypothesis. -/
abbrev ReflectionFamily {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ : ℝ)
    (R : ℂ → ℂ) (BR : ℝ → Ω → BrownianPath × BrownianPath) (ZR : Ω → Measure ℝ) : Prop :=
  ∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (BR α) ZR : ℂ)

/-- The diagonal four-point identity. -/
abbrev FourPointDiagonal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (γ μ α₁ α₂ α₃ : ℝ) (H : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(γ / 2)) α₁ α₂ α₃ z =
    structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
      (‖gaussFMinus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
          (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2 +
        gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
            (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
          ‖gaussFPlus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
            (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2)

end DOZZ.Proofs
