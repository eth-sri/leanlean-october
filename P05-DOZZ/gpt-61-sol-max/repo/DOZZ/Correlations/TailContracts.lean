/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.ReflectionBarR
public import DOZZ.Statements.Brownian.ReflectionExponent
public import DOZZ.Statements.Correlations.OneInsertionTailCoefficient
public import DOZZ.Statements.Correlations.TwoInsertionTailCeiling
public import DOZZ.Statements.Correlations.LocalSingularMass
public import DOZZ.Statements.Correlations.UniformPositiveC1Family

/-! Exact uniform tail interfaces, with their source reflection witnesses. -/
@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs.Contract
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)

/-- Shared oneInsertionTail proposition. -/
abbrev oneInsertionTail (γ : ℝ) (Kz : Set ℂ) (Kα : Set ℝ) (Family : ℂ → Set (ℂ → ℝ)) : Prop :=
  ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α ∈ Kα, IsReflectionData P γ α (B α) Z) ∧
        ∀ η : ℝ, 0 < η → (∀ α ∈ Kα, η < oneInsertionErrorCeiling γ α) →
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ F ∈ Family z, ∀ x : ℝ, 1 ≤ x →
              |(P {ω | ENNReal.ofReal x < localSingularMass M F z γ α ω}).toReal -
                oneInsertionTailCoefficient γ α z (F z) (reflectionBarR P γ α (B α) Z) *
                  Real.rpow x (-reflectionExponent γ α)| ≤
                C * Real.rpow x (-reflectionExponent γ α - η)

/-- Shared uniformOneInsertionTail proposition. -/
abbrev uniformOneInsertionTail (γ : ℝ) : Prop :=
  ∀
    (Kz : Set ℂ) (_hKz : IsCompact Kz) (_hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    (Kα : Set ℝ) (_hKα : IsCompact Kα)
    (_hα : ∀ α ∈ Kα, γ / 2 < α ∧ α < Q γ)
    (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (_hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound),
    oneInsertionTail P X M γ Kz Kα Family

/-- Shared uniformTwoInsertionTail proposition. -/
abbrev uniformTwoInsertionTail (γ : ℝ) : Prop :=
  ∀ (K2 K3 : Set ℂ) (_ : IsCompact K2) (_ : IsCompact K3)
      (_ : ∀ z ∈ K2, 2 ≤ ‖z‖) (_ : ∀ z ∈ K3, 2 ≤ ‖z‖)
      (_ : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2 - z3‖)
      (A2 A3 : Set ℝ) (_ : IsCompact A2) (_ : IsCompact A3)
      (_ : ∀ α ∈ A2, γ / 2 < α ∧ α < Q γ)
      (_ : ∀ α ∈ A3, γ / 2 < α ∧ α < Q γ)
      (F2s F3s : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
      (_ : UniformPositiveC1Family K2 F2s radius supBound derivBound lowerBound)
      (_ : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound),
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, (α ∈ A2 ∨ α ∈ A3) → IsReflectionData P γ α (B α) Z) ∧
          ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧
            ∀ z2 ∈ K2, ∀ z3 ∈ K3, ∀ α2 ∈ A2, ∀ α3 ∈ A3,
              ∀ F2 ∈ F2s z2, ∀ F3 ∈ F3s z3, ∀ x : ℝ, 1 ≤ x →
                |(P {ω | ENNReal.ofReal x <
                    localSingularMass M F2 z2 γ α2 ω + localSingularMass M F3 z3 γ α3 ω}).toReal -
                  (oneInsertionTailCoefficient γ α2 z2 (F2 z2) (reflectionBarR P γ α2 (B α2) Z) *
                      Real.rpow x (-reflectionExponent γ α2) +
                    oneInsertionTailCoefficient γ α3 z3 (F3 z3) (reflectionBarR P γ α3 (B α3) Z) *
                      Real.rpow x (-reflectionExponent γ α3))| ≤
                  C * Real.rpow x (-(twoInsertionTailCeiling γ α2 α3 - θ))

end DOZZ.Proofs.Contract
