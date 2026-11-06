/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.RootedIdentity
public import DOZZ.FourPoint.RetainedMass
import Mathlib.Tactic
/-! Positive finite retained source masses for the signed Pareto expectations. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- Positive finite retained source masses from the common Coulomb estimate. -/
abbrev dual_source_outerMass_positive_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ ξ : ℝ) :=
  retained_coulombMass_positive_finite_ae P X hX γ hγ hγ₂ M hM
    (-2 / γ) α₁ α₂ α₃ ξ (by
      rw [neg_div]
      unfold Q
      have hi : 0 < 2 / γ := div_pos (by norm_num) hγ
      linarith only [hγ, hi])

end DOZZ.Proofs
