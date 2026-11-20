/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.RetainedZeroMass
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
theorem dual_rooted_retainedZero_inverse_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℂ) (r : ℝ), r ≤ 1 →
      (∫⁻ ω, dualRetainedZeroMass γ α₁ α₂ α₃ r (gmcRootedMeasure γ u (M ω)) ^ (-q) ∂P) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, hC, h⟩ := inverse_fixed_disk_uniform P X hX γ hγ hγ₂ M hM _ q
    (mul_pos (Real.exp_pos (-γ ^ 2 * Real.log 2)) (coulombGuardWeight_pos γ ![-2 / γ, α₁, α₂] α₃)) hq
  refine ⟨C, hC, fun u r hr => h _ fun ω => ?_⟩
  exact rooted_coulombMass_fixed_disk_lower_restrict γ u (M ω) _ _ _
    (three_roots_in_unit_disk (z := 0) (by simp)) (isClosed_le continuous_const continuous_norm).measurableSet
    (fixed_disk_subset_exterior hr)

end DOZZ.Proofs
