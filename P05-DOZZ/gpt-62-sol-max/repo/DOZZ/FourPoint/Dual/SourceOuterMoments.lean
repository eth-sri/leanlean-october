/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.RootedIdentity
import Mathlib.Tactic
import DOZZ.FourPoint.Fusion.RetainedInverseMass
/-! Positive finite retained source masses for the signed Pareto expectations. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual retained source mass is positive and finite on one full-measure event. -/
theorem dual_source_outerMass_positive_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ ξ : ℝ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1)
    (hr : ‖z‖^(1-ξ) ≤ 1) :
    ∀ᵐ ω ∂P, 0 < dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ∧
      dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ < ⊤ :=
  fusionOuterMass_positive_finite_ae P X hX γ hγ hγ₂ M hM (-2 / γ) α₁ α₂ α₃ ξ
    (by
      simp only [Q, neg_div]
      have : 0 < 2 / γ := by positivity
      linarith) hα₁ hα₂ hα₃ z hz0 hz1 hz hr

end DOZZ.Proofs
