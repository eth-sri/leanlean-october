/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Reflected.OuterMassLimit
public import DOZZ.FourPoint.TaylorFixedDisk
import Mathlib.Tactic
import DOZZ.FourPoint.Fusion.RetainedInverseMass

/-! # A fixed disk retained by the reflected outer mass -/

public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Uniform inverse moments of the literal retained mass, at every nonnegative inverse order. -/
theorem reflected_outerMass_inverse_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ : ℝ), ‖z‖ ≤ 1 → ‖z‖ ^ (1 - ξ) ≤ 1 →
      (∫⁻ ω, gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) ≤
        ENNReal.ofReal C :=
  fusionOuterMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM (-γ / 2) α₁ α₂ α₃ q hq

end DOZZ.Proofs
