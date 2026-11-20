/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.InterpolatedFactor

/-! # The bounded factor in the rescaled local rooting integrals -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The unit-chart cutoff and the remaining insertion weight after `x = y*z`. -/
noncomputable def fusionScaledFactor {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ s : ℝ) (y z : ℂ) : ℝ :=
  if ‖y * z‖ < 1 / 2 then ‖y * z - 1‖ ^ (-γ * α₂) *
    (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y z (M ω) ^ s ∂P).toReal else 0

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

@[simp] theorem fusionInterpolatedFactor_one (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ s : ℝ) (y z : ℂ) :
    fusionInterpolatedFactor P M γ α₁ α₂ α₃ s 1 y z = fusionScaledFactor P M γ α₁ α₂ α₃ s y z := by
  simp [fusionInterpolatedFactor, fusionScaledFactor, fusionInterpolatedMass]

/-- A uniform inverse moment bound also controls the entire remaining scaled factor. -/
theorem fusionScaledFactor_uniform_bound (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (hs : s ≤ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y z : ℂ, ‖z‖ ≤ 1 →
      |fusionScaledFactor P M γ α₁ α₂ α₃ s y z| ≤ B := by
  obtain ⟨C, hC, h⟩ := fusionInterpolatedFactor_uniform_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s hs
  exact ⟨C, hC, by simpa using h 1 (by simp)⟩

end

end DOZZ.Proofs
