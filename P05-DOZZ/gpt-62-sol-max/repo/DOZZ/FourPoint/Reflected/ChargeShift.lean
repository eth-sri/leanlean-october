/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CircleTilt
public import DOZZ.FourPoint.Reflected.OuterInverseGuard
public import DOZZ.FourPoint.RootedPairMoments
public import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.Tactic
import DOZZ.FourPoint.Fusion.RetainedInverseMass
public import DOZZ.FourPoint.Fusion.RetainedCircleTilt
/-! # The literal retained-region charge shift under a circle tilt -/
@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The retained mass is a measurable functional of the measure, with no spatial clipping. -/
theorem reflected_outerMass_measure_measurable (γ α₁ α₂ α₃ ξ : ℝ) (z : ℂ) :
    Measurable (fun μ : Measure ℂ => gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ) :=
  fusionOuterMass_measurable γ (-γ / 2) α₁ α₂ α₃ ξ z

/-- Exact Cameron-Martin identification of the inverse outer moment at arbitrary real circle time. -/
theorem reflected_outerMass_circle_tilt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (a m α₁ α₂ α₃ ξ q : ℝ) (hm : 0 ≤ m) (z : ℂ)
    (hr : 0 < ‖z‖ ^ (1 - ξ)) (houtside : Real.exp (-m) ≤ ‖z‖ ^ (1 - ξ)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 m - m * a ^ 2 / 2)) *
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) =
      ∫⁻ ω, gammaHalfOuterMass γ (α₁ + a) α₂ α₃ (M ω) z ξ ^ (-q) ∂P :=
  fusionOuterMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hXc (-γ / 2) a m α₁ α₂ α₃ ξ q hm z hr houtside

end DOZZ.Proofs
