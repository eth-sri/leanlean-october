/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceOuterMoments
public import DOZZ.FourPoint.RetainedMass
public import DOZZ.GMC.RealMoment
import Mathlib.Tactic
/-! Finite actual radial-weighted inverse moments and their signed real expectation interface. -/
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- Finite radial-weighted inverse moments at the supplied retained scale. -/
theorem reflected_radial_scale_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (ν h s α₁ α₂ α₃ ξ q : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^s)*
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P) < ⊤ := by
  simpa only [retainedCoulombMass, gammaHalfOuterMass, reflected_radial_scale] using
    retained_coulombMass_radial_moment_finite P X hX γ hγ hγ₂ M hM Xc hc (-γ / 2) (γ ^ 2 / 2)
      ν h s α₁ α₂ α₃ ξ q hh hξ hξ1 hq z hz0 hz

/-- The actual radial-weighted inverse moment has an integrable real representative, and
its signed real expectation equals the ENNReal expectation converted to real. -/
abbrev reflected_radial_scale_real_expectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (ν h s α₁ α₂ α₃ ξ q : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1) :=
  have hf := reflected_radial_scale_moment_finite P X hX γ hγ hγ₂ M hM Xc hc
    ν h s α₁ α₂ α₃ ξ q hh hξ hξ1 hq z hz0 hz
  have hβ : AEMeasurable (fun ω => reflected_radial_scale γ ν h Xc z ω) P :=
    (((hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable.const_mul γ).sub aemeasurable_const).sub
      aemeasurable_const |>.exp
  weighted_real_moment_of_finite (A := fun ω => gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ)
    (b := fun ω => reflected_radial_scale γ ν h Xc z ω)
    ((reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)) hβ
    (fun _ => (Real.exp_pos _).le) hf.ne

end DOZZ.Proofs
