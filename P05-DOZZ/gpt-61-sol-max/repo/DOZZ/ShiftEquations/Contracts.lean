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
public import DOZZ.ShiftEquations.ContinuationContracts

/-! Shared analytic and probabilistic hypotheses used by the shift reductions. -/
@[expose] public section
open MeasureTheory Filter Topology Set
namespace DOZZ.Proofs.Contract

/-- The meromorphic first shift identity for the reflection coefficient. -/
abbrev reflectionShift (γ μ : ℝ) (R : ℂ → ℂ) : Prop :=
  ∀ᶠ z in codiscrete ℂ,
      R (z - γ / 2) = -(μ * Real.pi : ℂ) * R z /
        (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
          lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2))

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)

include Ω _inst1 P X M in
/-- Structure and reflection continuations on a common strip, with fixed charge slack. -/
abbrev fixedShiftGluing  (γ μ η : ℝ) : Prop :=
  ∀ α₂ α₃ : ℝ, (Q γ - η < α₂ ∧ α₂ < Q γ) → (Q γ - η < α₃ ∧ α₃ < Q γ) →
      Contract.fixedChargeShiftGluing P X M γ μ η α₂ α₃

include Ω _inst1 P X M in
/-- The common-strip gluing input, uniformly in the charge slack. -/
abbrev shiftGluing  (γ μ : ℝ) : Prop :=
  ∀ η : ℝ, (0 < η ∧ Q γ - 2 * η > γ) → fixedShiftGluing P X M γ μ η

include Ω _inst1 P X M in
/-- The second dual crossing seed with reflection data on one source model. -/
abbrev dualSecondSeed  (γ μ : ℝ) : Prop :=
  ∀ α ε α' : ℝ, α < Q γ → ε < Q γ → α' < Q γ → 2 * Q γ + 2 / γ < α + ε + α' →
      ∃ Bε Bα : Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ ε Bε Z ∧
          IsReflectionData P γ α Bα Z ∧
          reflectionR P γ μ ε Bε Z * structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
            dualCrossingL γ ε α α' * reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α'

/-- The half-charge unit-volume crossing input. -/
abbrev unitCrossing {Ω : Type*} [MeasurableSpace Ω]
     (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ : ℝ) : Prop :=
  ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α

include Ω _inst1 P X M in
/-- A meromorphic continuation of reflection data satisfying the first shift. -/
abbrev firstShift  (γ μ : ℝ) : Prop :=
  ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              reflectionShift γ μ R

include Ω _inst1 P X M in
/-- The residue bridge between unit-volume constants and the reflection moment. -/
abbrev residueBridge  (γ : ℝ) : Prop :=
  ∀ α2 α3 : ℝ, 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
        Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
            (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
          (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
            reflectionBarR P γ α3 (B α3) Z))

include Ω _inst1 P X M in
/-- Holomorphic representation of the reflection moment on every compact charge set. -/
abbrev rbarRepresentation  (γ : ℝ) : Prop :=
  ∀ I : Set ℝ, IsCompact I → (∀ α ∈ I, γ / 2 < α ∧ α < Q γ) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ (∀ α ∈ I, IsReflectionData P γ α (B α) Z) ∧
          ∃ V : Set ℂ, IsOpen V ∧ (∀ α ∈ I, (α : ℂ) ∈ V) ∧
            ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
              (∀ α ∈ I, f (α : ℂ) = (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
              DifferentiableOn ℂ (fun z => rbarCoefficient γ z * f z) V ∧
              (∀ α ∈ I, rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                (reflectionBarR P γ α (B α) Z : ℂ))

/-- The reflection-moment representation, uniformly in the GMC parameter. -/
abbrev allRbarRepresentations {Ω : Type*} [MeasurableSpace Ω]
     (P : Measure Ω) (X : Ω → Distr) : Prop :=
  ∀ (γ : ℝ) (Mγ : Ω → Measure ℂ), 0 < γ → γ < 2 →
    IsGMCOf P X γ Mγ → rbarRepresentation P X Mγ γ

end DOZZ.Proofs.Contract
