/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceOuterMoments
import Mathlib.Tactic
/-! Finite actual radial-weighted inverse moments and their signed real expectation interface. -/
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc) (ν h s α₁ α₂ α₃ ξ q : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q) (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1)
include hX hγ hγ₂ hM hc hh hξ hξ1 hq hz0 hz

/-- Every radial likelihood order and nonnegative outer inverse order is finite at the
actual retained source scale. Cameron-Martin handles the correlation, then the fixed disk gives
finiteness for the shifted charge. -/
theorem reflected_radial_scale_moment_finite
    :
    (∫⁻ ω, ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^s)*
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P) < ⊤ := by
  let t := -Real.log ‖z‖
  let m := t+h
  let aTilt := γ*s
  let D := Real.exp (m*aTilt^2/2-s*γ*ν*m-s*γ^2/2*t)
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hm : 0 ≤ m := by
    have hl := Real.log_nonpos hn.le hz
    linarith
  have hr0 : 0 < ‖z‖^(1-ξ) := Real.rpow_pos_of_pos hn _
  have hr1 : ‖z‖^(1-ξ) ≤ 1 := by
    simpa using Real.rpow_le_rpow hn.le hz (sub_nonneg.mpr hξ1.le)
  have hr : ‖z‖ ≤ ‖z‖^(1-ξ) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hn hz
      (by linarith : 1-ξ ≤ 1)
  have hout : Real.exp (-m) ≤ ‖z‖^(1-ξ) := by
    have hsmall : -m ≤ Real.log ‖z‖ := by linarith
    have hs : Real.exp (-m) ≤ ‖z‖ := by
      simpa only [Real.exp_log hn] using Real.exp_le_exp.mpr hsmall
    linarith
  have he (ω : Ω) : (reflected_radial_scale γ ν h Xc z ω)^s =
      D*Real.exp (aTilt*Xc ω 0 m-m*aTilt^2/2) := by
    dsimp only [reflected_radial_scale,D,m,t,aTilt]
    rw [← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hshift := reflected_outerMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hc
    aTilt m α₁ α₂ α₃ ξ q hm z hr0 hout
  obtain ⟨C, _, hb⟩ := reflected_outerMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
    (α₁+aTilt) α₂ α₃ q hq
  have hf : (∫⁻ ω, gammaHalfOuterMass γ (α₁+aTilt) α₂ α₃ (M ω) z ξ ^(-q) ∂P) < ⊤ :=
    (hb z ξ hz hr1).trans_lt ENNReal.ofReal_lt_top
  have hD : 0 ≤ D := by positivity
  simp_rw [he, ENNReal.ofReal_mul hD, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hshift]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

/-- The actual radial-weighted inverse moment has an integrable real representative, and
its signed real expectation equals the ENNReal expectation converted to real. -/
theorem reflected_radial_scale_real_expectation
    :
    Integrable (fun ω => (reflected_radial_scale γ ν h Xc z ω)^s*
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q)) P ∧
    (∫ ω, (reflected_radial_scale γ ν h Xc z ω)^s*
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q) ∂P) =
    (∫⁻ ω, ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^s)*
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P).toReal := by
  have hf := reflected_radial_scale_moment_finite P X hX γ hγ hγ₂ M hM Xc hc
    ν h s α₁ α₂ α₃ ξ q hh hξ hξ1 hq z hz0 hz
  have hcoord :=
    (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
  have hβ : AEMeasurable (fun ω => reflected_radial_scale γ ν h Xc z ω) P := by
    dsimp only [reflected_radial_scale]
    fun_prop
  have hpow : Measurable (fun x => ENNReal.ofReal (x^s)) := by fun_prop
  have hmass := (reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have hm := (hpow.comp_aemeasurable hβ).mul (hmass.pow_const (-q))
  change AEMeasurable (fun ω => ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^s)*
    gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q)) P at hm
  have hβnonneg (ω : Ω) : 0 ≤ reflected_radial_scale γ ν h Xc z ω := by
    dsimp only [reflected_radial_scale]
    positivity
  have hreal (ω : Ω) :
      (ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^s)*
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q)).toReal =
      (reflected_radial_scale γ ν h Xc z ω)^s*
        (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (hβnonneg ω) _)]
  constructor
  · simpa only [hreal] using integrable_toReal_of_lintegral_ne_top hm hf.ne
  · simpa only [hreal] using integral_toReal hm (ae_lt_top' hm hf.ne)

end

end

end DOZZ.Proofs
