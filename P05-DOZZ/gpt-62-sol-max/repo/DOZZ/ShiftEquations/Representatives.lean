/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Defs.ShiftCoeffA
public import DOZZ.Statements.FourPoint.DualCrossingL
public import DOZZ.Statements.Complex.HorizontalStrip
public import Mathlib.Analysis.Meromorphic.Complex
public import DOZZ.DOZZAlgebra.ReflectionShiftForm

/-! Shared predicates for the meromorphic representatives and the second crossing seed. -/

@[expose] public section

open MeasureTheory Filter

namespace DOZZ

/-- A reflection witness at every charge in the physical reflection interval. -/
abbrev IsReflectionFamily {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) : Prop :=
  ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z

/-- Agreement of `R` with the probabilistic reflection coefficient on that interval. -/
abbrev RepresentsReflection {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ : ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (R : ℂ → ℂ) : Prop :=
  ∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)

/-- Agreement of `C` with the structure constant as the first charge ranges from `2η` to `Q`. -/
abbrev RepresentsStructureConstant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ μ η α₂ α₃ : ℝ) (C : ℂ → ℂ) : Prop :=
  ∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)

/-- Meromorphic reflection representative satisfying an additional law on a strip. -/
abbrev HasReflectionRepresentative {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ : ℝ) (H : (ℂ → ℂ) → Prop) : Prop :=
  ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
    IsSourceLateralProjection P X γ M Z ∧ IsReflectionFamily P γ B Z ∧
      ∃ h > 0, ∃ R : ℂ → ℂ, MeromorphicOn R (horizontalStrip h) ∧
        RepresentsReflection P γ μ B Z R ∧ H R

abbrev HasFirstReflectionShift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ : ℝ) : Prop :=
  HasReflectionRepresentative P X M γ μ (ReflectionFirstShift γ μ)

abbrev HasDualReflectionShift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ : ℝ) : Prop :=
  HasReflectionRepresentative P X M γ μ fun R =>
    ∃ c : ℂ, c ≠ 0 ∧ c = ((γ : ℂ) ^ 2 / 4) * (μ * Real.pi : ℂ) * R γ ∧ ReflectionDualShift γ c R

/-- The first structure shift off a discrete exceptional set. -/
abbrev StructureFirstShift (γ μ α₂ α₃ : ℝ) (C : ℂ → ℂ) : Prop :=
  ∀ᶠ z in codiscrete ℂ, C (z + γ / 2) =
    -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z α₂ α₃ * C (z - γ / 2)

abbrev HasFirstStructureShift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ μ η α₂ α₃ : ℝ) : Prop :=
  ∃ h > 0, ∃ C : ℂ → ℂ, MeromorphicOn C (horizontalStrip h) ∧
    RepresentsStructureConstant P M γ μ η α₂ α₃ C ∧ StructureFirstShift γ μ α₂ α₃ C

/-- The reflected first shift, as an identity off a discrete exceptional set. -/
abbrev ReflectedFirstShift (γ μ α₂ α₃ : ℝ) (C R : ℂ → ℂ) : Prop :=
  ∀ᶠ z in codiscrete ℂ, R (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
    -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) * C (z - γ / 2)

/-- Common-strip extensions satisfying the reflection relation and the reflected first shift. -/
abbrev HasGluedRepresentatives {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η α₂ α₃ : ℝ) : Prop :=
  ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
    IsSourceLateralProjection P X γ M Z ∧ IsReflectionFamily P γ B Z ∧
      ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
        MeromorphicOn C (horizontalStrip h) ∧ MeromorphicOn R (horizontalStrip h) ∧
        RepresentsStructureConstant P M γ μ η α₂ α₃ C ∧ RepresentsReflection P γ μ B Z R ∧
        (∀ᶠ z in codiscrete ℂ, C z = R z * C (2 * Q γ - z)) ∧
        ReflectedFirstShift γ μ α₂ α₃ C R

abbrev HasShiftGluingAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ) : Prop :=
  ∀ α₂ α₃ : ℝ, (Q γ - η < α₂ ∧ α₂ < Q γ) → (Q γ - η < α₃ ∧ α₃ < Q γ) →
    HasGluedRepresentatives P X M γ μ η α₂ α₃

abbrev HasShiftGluing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ) : Prop :=
  ∀ η : ℝ, (0 < η ∧ Q γ - 2 * η > γ) → HasShiftGluingAt P X M γ μ η

/-- The second (dual) crossing relation, with reflection coefficients on the same lateral chaos. -/
abbrev DualCrossingRelation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ α ε α' : ℝ) : Prop :=
  ∃ Bε Bα : Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
    IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ ε Bε Z ∧
    IsReflectionData P γ α Bα Z ∧
    reflectionR P γ μ ε Bε Z * structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
      dualCrossingL γ ε α α' * reflectionR P γ μ α Bα Z *
        structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α'

abbrev HasDualCrossing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ) : Prop :=
  ∀ α ε α' : ℝ, α < Q γ → ε < Q γ → α' < Q γ → 2 * Q γ + 2 / γ < α + ε + α' →
    DualCrossingRelation P X M γ μ α ε α'

abbrev DualCrossingSeedTwo.{u} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ), 0 < γ → γ < 2 → 0 < μ → α < Q γ → ε < Q γ → α' < Q γ →
    2 * Q γ + 2 / γ < α + ε + α' → IsEquatorGFF P X → IsGMCOf P X γ M →
    DualCrossingRelation P X M γ μ α ε α'

end DOZZ
