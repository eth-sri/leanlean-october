/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.MovingMoment
public import DOZZ.FourPoint.Dual.RetainedZeroMass
public import DOZZ.FourPoint.Dual.OuterMassLimit
public import DOZZ.FourPoint.Dual.MassComparison
public import DOZZ.FourPoint.Dual.RootedIdentity

import Mathlib.Tactic

/-! # The moving inverse-moment error at the relative cutoff scale -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The inverse expectation of the actual retained dual mass. -/
noncomputable def dualOuterMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) (ξ : ℝ) : ℝ :=
  (∫⁻ ω, dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-p) ∂P).toReal

/-- The moving error is bounded by `‖z‖/r` times a uniform inverse moment, at the literal
outer radius `r=‖z‖^(1-ξ)`. The estimate does not impose any upper bound on `ξ`. -/
theorem dual_outer_moving_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hp : 0 < p)
    (hα₁ : α₁ - 2 / γ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ : ℝ),
      0 < ‖z‖ ^ (1 - ξ) → ‖z‖ ^ (1 - ξ) ≤ 1 → ‖z‖ ≤ 1 →
      ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2 →
      |dualOuterMoment P M γ α₁ α₂ α₃ p z ξ -
        (∫⁻ ω, (dualRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) (M ω)) ^ (-p) ∂P).toReal| ≤
          C * (‖z‖ / ‖z‖ ^ (1 - ξ)) := by
  have h : γ * (2 / γ) = 2 := by field_simp [hγ.ne']
  simpa only [neg_div, dualOuterMass, dualRetainedZeroMass, dualOuterMoment, fusionOuterMass] using fusion_outer_moving_moment_bound P X M γ (2 / γ) α₁ α₂ α₃ p
    hγ hγ₂ hp (by rw [h]; norm_num) h.le hα₁ hα₂ hα₃ hX hM

end DOZZ.Proofs
