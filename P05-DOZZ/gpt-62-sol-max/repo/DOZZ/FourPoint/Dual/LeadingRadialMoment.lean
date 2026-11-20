/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.RetainedRadialMoments
public import DOZZ.FourPoint.Dual.SourceRadialMoments
public import DOZZ.FourPoint.Reflected.LeadingRadialMoment
import Mathlib.Tactic
/-! The normalized leading Pareto weight has the actual reflected charge-shift limit. -/
@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- On the punctured plane the exponential scale equals the literal quadratic restart. -/
theorem dual_radial_scale_eq_restart {Ω : Type*} (γ ν h : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (z : ℂ) (hz : z ≠ 0) (ω : Ω) :
    dual_radial_scale γ ν h Xc z ω = ‖z‖ ^ (2 : ℝ) *
      Real.exp (γ * (Xc ω 0 (-Real.log ‖z‖ + h) - ν * (-Real.log ‖z‖ + h))) := by
  unfold dual_radial_scale
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz), ← Real.exp_add]
  congr 1
  ring

/-- The normalized leading Pareto expectation has its genuine finite real limit. -/
theorem dual_leading_radial_moment_toReal_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (ν α₁ α₂ α₃ ξ q h : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁+2*ν-2/γ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ =>
      (∫⁻ ω, ENNReal.ofReal ((dual_radial_scale γ ν h Xc z ω)^(2*ν/γ))*
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P).toReal / ‖z‖^((4/γ)*ν))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (∫⁻ ω, rho γ (M ω) (α₁+2*ν-2/γ) α₂ α₃ ^(-q) ∂P).toReal) := by
  have hexp : 2 * (2 * ν / γ) = (4 / γ) * ν := by field_simp <;> ring
  have ht := fusion_leading_radial_moment_toReal_tendsto
    P X hX γ hγ hγ₂ M hM Xc hc (2 / γ) ν α₁ α₂ α₃ ξ q h 2 (by positivity)
    hh hξ hξ1 hq hα₁ hα₂ hα₃
  rw [hexp] at ht
  simpa only [fusionRadialScale, dual_radial_scale, fusionOuterMass,
    dualOuterMass, ← neg_div] using ht

end DOZZ.Proofs
