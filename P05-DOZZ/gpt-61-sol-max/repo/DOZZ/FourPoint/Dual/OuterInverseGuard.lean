/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.OuterMassLimit
public import DOZZ.FourPoint.RetainedMass
import Mathlib.Tactic

/-! # A fixed disk retained by the dual outer mass -/

public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The same positive disk weight works for every moving root and every retained radius at most one. -/
theorem dual_outerMass_fixed_disk_lower (γ α₁ α₂ α₃ ξ : ℝ) (μ : Measure ℂ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hr : ‖z‖ ^ (1 - ξ) ≤ 1) :
    ENNReal.ofReal ((2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-2 / γ, α₁, α₂] : Fin 3 → ℝ) i|) *
      (4 : ℝ) ^ (-|γ * α₃|)) * μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
        dualOuterMass γ α₁ α₂ α₃ μ z ξ := by
  exact coulombMass_restrict_norm_fixed_disk_lower γ μ ![-2 / γ, α₁, α₂] ![z, 0, 1]
    α₃ _ hr (by simpa [Fin.forall_fin_succ] using hz)

/-- Uniform inverse moments from the common retained-disk estimate. -/
abbrev dual_outerMass_inverse_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :=
  retained_coulombMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM (-2 / γ)

end DOZZ.Proofs
