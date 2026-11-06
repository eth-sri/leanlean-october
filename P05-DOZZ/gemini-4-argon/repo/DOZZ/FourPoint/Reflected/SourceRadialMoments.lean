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


/-- The actual radial-weighted inverse moment has an integrable real representative, and
its signed real expectation equals the ENNReal expectation converted to real. -/
theorem reflected_radial_scale_real_expectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    Xc (hc : IsCircleAverage P X Xc)
    (ν h s α₁ α₂ α₃ ξ q : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    z (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1) :
    Integrable (fun ω => (reflected_radial_scale γ ν h Xc z ω)^s*
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q)) P ∧
    (∫ ω, (reflected_radial_scale γ ν h Xc z ω)^s*
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q) ∂P) =
    (∫⁻ ω, ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^s)*
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P).toReal := by
  have reflected_radial_scale_moment_finite ν h (s : ℝ) α₁ α₂ α₃ ξ (q : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q) z (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1) : (∫⁻ ω, ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^s)* gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P) < ⊤ := by
    let t := -Real.log ‖z‖
    let m := t+h
    let aTilt := γ*s
    let D := Real.exp (m*aTilt^2/2-s*γ*ν*m-s*γ^2/2*t)
    have hn := norm_pos_iff.mpr hz0
    have he ω : (reflected_radial_scale γ ν h Xc z ω)^s =
        D*Real.exp (aTilt*Xc ω 0 m-m*aTilt^2/2) := by
      dsimp only [reflected_radial_scale,D,m,t,aTilt]
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    obtain ⟨C, _, hb⟩ := reflected_outerMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
      (α₁+aTilt) α₂ α₃ q hq
    have hD : 0 ≤ D := (Real.exp_pos _).le
    simp_rw [he, ENNReal.ofReal_mul hD, mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, (reflected_outerMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hc aTilt m α₁ α₂ α₃ ξ q (by dsimp only [m,t]; linarith only [(Real.log_nonpos hn.le hz),hh]) z (Real.rpow_pos_of_pos hn _) (by exact (show Real.exp (-m) ≤ ‖z‖ by simpa only [Real.exp_log hn] using Real.exp_le_exp.mpr (show -m ≤ Real.log ‖z‖ by dsimp only [m,t]; linarith only [hh])).trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hn hz (by linarith only [hξ] : 1-ξ ≤ 1))))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((hb z ξ hz (by simpa only [Real.one_rpow] using Real.rpow_le_rpow hn.le hz (sub_nonneg.mpr hξ1.le))).trans_lt ENNReal.ofReal_lt_top)
  have hf := reflected_radial_scale_moment_finite
    ν h s α₁ α₂ α₃ ξ q hh hξ hξ1 hq z hz0 hz
  have hβ : AEMeasurable (fun ω => reflected_radial_scale γ ν h Xc z ω) P := by
    dsimp only [reflected_radial_scale]
    exact ((((hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable).const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
  have hmass := (reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have hm := ((show Measurable (fun x => ENNReal.ofReal (x^s)) by fun_prop).comp_aemeasurable hβ).mul (hmass.pow_const (-q))
  change AEMeasurable (fun ω => ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^s)*
    gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q)) P at hm
  have hβnonneg ω : 0 ≤ reflected_radial_scale γ ν h Xc z ω := by
    dsimp only [reflected_radial_scale]
    exact (Real.exp_pos _).le
  have hreal ω :
      (ENNReal.ofReal ((reflected_radial_scale γ ν h Xc z ω)^s)*
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q)).toReal =
      (reflected_radial_scale γ ν h Xc z ω)^s*
        (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (hβnonneg ω) _)]
  constructor
  · simpa only [hreal] using integrable_toReal_of_lintegral_ne_top hm hf.ne
  · simpa only [hreal] using integral_toReal hm (ae_lt_top' hm hf.ne)

end DOZZ.Proofs
