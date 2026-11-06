/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.RootedLower
import Mathlib.Tactic

/-! # Uniform inverse moments of the rooted dual exterior mass

A fixed insertion-free disk controls the source's rooted inverse moment for
all rooting points, including exterior points and the totalized diagonal.
-/

public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Uniform inverse moments of the literal retained mass, at every nonnegative inverse order. -/
theorem dual_rooted_outerMass_inverse_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z u : ℂ) (ξ : ℝ), ‖z‖ ≤ 1 → ‖z‖ ^ (1 - ξ) ≤ 1 →
      (∫⁻ ω, dualOuterMass γ α₁ α₂ α₃ (gmcRootedMeasure γ u (M ω)) z ξ ^ (-q) ∂P) ≤
        ENNReal.ofReal C := by
  let w : ℝ := Real.exp (-γ ^ 2 * Real.log 2) * ((2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-2 / γ, α₁, α₂] : Fin 3 → ℝ) i|) *
    (4 : ℝ) ^ (-|γ * α₃|))
  obtain ⟨C, hC, hb⟩ := gmc_inverse_moment_uniform_of_disk_lower
    P X hX γ hγ hγ₂ M hM q w hq (by dsimp only [w]; positivity)
  refine ⟨C, hC, ?_⟩
  intro z u ξ hz hr
  exact hb _ fun ω => dual_rooted_outerMass_fixed_disk_lower γ α₁ α₂ α₃ ξ (M ω) z u hz hr

end DOZZ.Proofs
