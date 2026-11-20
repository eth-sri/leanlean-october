/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.RetainedRadialMoments
public import DOZZ.FourPoint.Reflected.ChargeShift
public import DOZZ.FourPoint.Reflected.RadialTilt
import Mathlib.Tactic
/-! The normalized leading Pareto weight has the actual reflected charge-shift limit. -/
@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual radial restart scale appearing in the inner mass. -/
noncomputable def reflected_radial_scale {Ω : Type*} (γ ν h : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  Real.exp (γ*Xc ω 0 (-Real.log ‖z‖+h)-γ*ν*(-Real.log ‖z‖+h)-γ^2/2*(-Real.log ‖z‖))

/-- The normalized leading Pareto expectation has its genuine finite real limit. -/
theorem reflected_leading_radial_moment_toReal_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (ν α₁ α₂ α₃ ξ q h : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁+2*ν-γ/2 < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ =>
      (∫⁻ ω, ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^(2*ν/γ))*
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P).toReal / ‖z‖^(γ*ν))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (∫⁻ ω, rho γ (M ω) (α₁+2*ν-γ/2) α₂ α₃ ^(-q) ∂P).toReal) := by
  have hexp : (γ ^ 2 / 2) * (2 * ν / γ) = γ * ν := by field_simp <;> ring
  have ht := fusion_leading_radial_moment_toReal_tendsto
    P X hX γ hγ hγ₂ M hM Xc hc (γ / 2) ν α₁ α₂ α₃ ξ q h (γ ^ 2 / 2) (by positivity)
    hh hξ hξ1 hq hα₁ hα₂ hα₃
  rw [hexp] at ht
  simpa only [fusionRadialScale, reflected_radial_scale, fusionOuterMass,
    gammaHalfOuterMass, ← neg_div] using ht

end DOZZ.Proofs
