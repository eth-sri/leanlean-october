/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.OuterInverseGuard
public import DOZZ.FourPoint.Fusion.RootedLowerBound
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
  obtain ⟨C, hC, h⟩ := inverse_fixed_disk_uniform P X hX γ hγ hγ₂ M hM _ q
    (mul_pos (Real.exp_pos (-γ ^ 2 * Real.log 2)) (coulombGuardWeight_pos γ ![-2 / γ, α₁, α₂] α₃)) hq
  refine ⟨C, hC, fun z u ξ hz hr => h _ fun ω => ?_⟩
  exact rooted_coulombMass_fixed_disk_lower_restrict γ u (M ω) _ _ _
    (three_roots_in_unit_disk hz) (isClosed_le continuous_const continuous_norm).measurableSet
    (fixed_disk_subset_exterior hr)

end DOZZ.Proofs
