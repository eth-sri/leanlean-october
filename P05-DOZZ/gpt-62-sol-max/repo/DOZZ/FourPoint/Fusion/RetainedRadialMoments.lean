/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import DOZZ.GMC.Moments.RhoCoulomb
import Mathlib.Tactic
public import DOZZ.FourPoint.Fusion.RetainedCircleTilt
import Mathlib.Tactic

/-! Radial restart likelihood and its inverse moments against the retained mass. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The restart scale for a kernel carrying the radial power `e`. -/
noncomputable def fusionRadialScale {Ω : Type*} (γ e ν h : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  Real.exp (γ * Xc ω 0 (-Real.log ‖z‖ + h) - γ * ν * (-Real.log ‖z‖ + h) -
    e * (-Real.log ‖z‖))

theorem fusionRadialScale_pos {Ω : Type*} (γ e ν h : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (z : ℂ) (ω : Ω) : 0 < fusionRadialScale γ e ν h Xc z ω :=
  Real.exp_pos _

theorem fusionRadialScale_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (γ e ν h : ℝ) (z : ℂ) : AEMeasurable (fusionRadialScale γ e ν h Xc z) P := by
  have hm := (hc.2.1 0 (-Real.log ‖z‖ + h)).aemeasurable
  exact (((hm.const_mul γ).sub aemeasurable_const).sub aemeasurable_const).exp

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ)
  (hc : IsCircleAverage P X Xc) (β e ν h s α₁ α₂ α₃ ξ q : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1)
  (hq : 0 ≤ q) (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1)
include Ω X hX hγ hγ₂ hM hc hh hξ hξ1 hq hz0 hz

/-- Every radial likelihood order and nonnegative outer inverse order is finite at the
actual retained source scale. Cameron-Martin handles the correlation, then the fixed disk gives
finiteness for the shifted charge. -/
theorem fusion_radial_moment_finite :
    (∫⁻ ω, ENNReal.ofReal ((fusionRadialScale γ e ν h Xc z ω)^s)*
      fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P) < ⊤ := by
  let t := -Real.log ‖z‖
  let m := t+h
  let aTilt := γ*s
  let D := Real.exp (m*aTilt^2/2-s*γ*ν*m-s*e*t)
  obtain ⟨hm, hr0, hout, hr1⟩ := retained_circle_window hz0 hz hh hξ.le hξ1.le
  have he (ω : Ω) : (fusionRadialScale γ e ν h Xc z ω)^s =
      D*Real.exp (aTilt*Xc ω 0 m-m*aTilt^2/2) := by
    dsimp only [fusionRadialScale,D,m,t,aTilt]
    rw [← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have hshift := fusionOuterMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hc
    β aTilt m α₁ α₂ α₃ ξ q hm z hr0 hout
  obtain ⟨C, _, hb⟩ := fusionOuterMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
    β (α₁+aTilt) α₂ α₃ q hq
  have hf : (∫⁻ ω, fusionOuterMass γ β (α₁+aTilt) α₂ α₃ (M ω) z ξ ^(-q) ∂P) < ⊤ :=
    (hb z ξ hz hr1).trans_lt ENNReal.ofReal_lt_top
  have hD : 0 ≤ D := (Real.exp_pos _).le
  simp_rw [he, ENNReal.ofReal_mul hD, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hshift]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf

/-- The actual radial-weighted inverse moment has an integrable real representative, and
its signed real expectation equals the ENNReal expectation converted to real. -/
theorem fusion_radial_real_expectation :
    Integrable (fun ω => (fusionRadialScale γ e ν h Xc z ω)^s*
      (fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q)) P ∧
    (∫ ω, (fusionRadialScale γ e ν h Xc z ω)^s*
      (fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q) ∂P) =
    (∫⁻ ω, ENNReal.ofReal ((fusionRadialScale γ e ν h Xc z ω)^s)*
      fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P).toReal := by
  have hf := fusion_radial_moment_finite P X hX γ hγ hγ₂ M hM Xc hc
    β e ν h s α₁ α₂ α₃ ξ q hh hξ hξ1 hq z hz0 hz
  have hβ := fusionRadialScale_aemeasurable P X Xc hc γ e ν h z
  have hpow : Measurable (fun x : ℝ => ENNReal.ofReal (x^s)) := by fun_prop
  have hmass := (fusionOuterMass_measurable γ β α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have hm := (hpow.comp_aemeasurable hβ).mul (hmass.pow_const (-q))
  change AEMeasurable (fun ω => ENNReal.ofReal ((fusionRadialScale γ e ν h Xc z ω)^s)*
    fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^(-q)) P at hm
  have hreal (ω : Ω) :
      (ENNReal.ofReal ((fusionRadialScale γ e ν h Xc z ω)^s)*
        fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^(-q)).toReal =
      (fusionRadialScale γ e ν h Xc z ω)^s*
        (fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ).toReal ^(-q) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (fusionRadialScale_pos ..).le _)]
  constructor
  · simpa only [hreal] using integrable_toReal_of_lintegral_ne_top hm hf.ne
  · simpa only [hreal] using integral_toReal hm (ae_lt_top' hm hf.ne)

end

/-- The leading source moment is an exact norm power times the circle likelihood moment. -/
theorem fusion_leading_radial_moment_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ ν h d : ℝ) (hγ : γ ≠ 0) (Xc : Ω → ℂ → ℝ → ℝ)
    (F : Ω → ℝ≥0∞) (z : ℂ) (hz : z ≠ 0) :
    (∫⁻ ω, ENNReal.ofReal ((fusionRadialScale γ d ν h Xc z ω)^(2*ν/γ))*F ω ∂P) =
      ENNReal.ofReal (‖z‖^(d * (2 * ν / γ))) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp
          (2*ν*Xc ω 0 (-Real.log ‖z‖+h)-(-Real.log ‖z‖+h)*(2*ν)^2/2))*F ω ∂P := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he (ω : Ω) : (fusionRadialScale γ d ν h Xc z ω)^(2*ν/γ) =
      ‖z‖^(d * (2 * ν / γ))*Real.exp
        (2*ν*Xc ω 0 (-Real.log ‖z‖+h)-(-Real.log ‖z‖+h)*(2*ν)^2/2) := by
    dsimp only [fusionRadialScale]
    rw [← Real.exp_mul, Real.rpow_def_of_pos hn, ← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [he, ENNReal.ofReal_mul (Real.rpow_nonneg hn.le _), mul_assoc]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω X hX hγ hγ₂ hM

/-- The normalized actual leading moment converges to the reflected rho, independently of
the fixed radial buffer. -/
theorem fusion_leading_radial_moment_tendsto
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (χ ν α₁ α₂ α₃ ξ q h d : ℝ) (hγχ : 0 ≤ γ * χ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁ + 2 * ν - χ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ =>
      (∫⁻ ω, ENNReal.ofReal ((fusionRadialScale γ d ν h Xc z ω)^(2*ν/γ))*
        fusionOuterMass γ (-χ) α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P) /
          ENNReal.ofReal (‖z‖^(d * (2 * ν / γ))))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (∫⁻ ω, rho γ (M ω) (α₁ + 2 * ν - χ) α₂ α₃ ^(-q) ∂P)) := by
  have ht := fusion_tilted_outer_inverse_moment_tendsto P X hX γ hγ hγ₂ M hM Xc hc
    χ (2 * ν) α₁ α₂ α₃ ξ q h hγχ hh hξ hξ1 hq hα₁ hα₂ hα₃
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  rw [fusion_leading_radial_moment_identity P γ ν h d hγ.ne' Xc _ z hz0]
  have hp : 0 < ‖z‖^(d * (2 * ν / γ)) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _
  symm
  rw [mul_comm (ENNReal.ofReal (‖z‖^(d * (2 * ν / γ))))]
  exact ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top

/-- A fixed exterior disk makes every nonnegative inverse order of rho integrable, without
a total-charge hypothesis. -/
theorem rho_inverse_expectation_lt_top
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^(-q) ∂P) < ⊤ := by
  obtain ⟨C, _, hb⟩ := coulomb_inverse_moment_uniform_roots P X hX γ hγ hγ₂ M hM
    (![α₁,α₂] : Fin 2 → ℝ) α₃ q hq
  have hroots : ∀ j : Fin 2, ‖(![0,1] : Fin 2 → ℂ) j‖ ≤ 1 := by
    intro j
    fin_cases j <;> simp
  have he : (∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^(-q) ∂P) =
      ∫⁻ ω, coulombMass γ (M ω) ![α₁,α₂] ![0,1] α₃ ^(-q) ∂P := by
    apply lintegral_congr_ae
    exact (gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ₂ M hM α₁ α₂ α₃).mono
      fun ω hω => congrArg (fun x : ℝ≥0∞ => x^(-q)) hω
  rw [he]
  exact (hb _ hroots).trans_lt ENNReal.ofReal_lt_top

/-- The normalized leading Pareto expectation has its genuine finite real limit. -/
theorem fusion_leading_radial_moment_toReal_tendsto
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (χ ν α₁ α₂ α₃ ξ q h d : ℝ) (hγχ : 0 ≤ γ * χ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁ + 2 * ν - χ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ =>
      (∫⁻ ω, ENNReal.ofReal ((fusionRadialScale γ d ν h Xc z ω)^(2*ν/γ))*
        fusionOuterMass γ (-χ) α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P).toReal / ‖z‖^(d * (2 * ν / γ)))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (∫⁻ ω, rho γ (M ω) (α₁ + 2 * ν - χ) α₂ α₃ ^(-q) ∂P).toReal) := by
  have ht := fusion_leading_radial_moment_tendsto P X hX γ hγ hγ₂ M hM Xc hc
    χ ν α₁ α₂ α₃ ξ q h d hγχ hh hξ hξ1 hq hα₁ hα₂ hα₃
  have hf := rho_inverse_expectation_lt_top P X hX γ hγ hγ₂ M hM
    (α₁ + 2 * ν - χ) α₂ α₃ q hq
  have hr := (ENNReal.tendsto_toReal hf.ne).comp ht
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using hr

end

end DOZZ.Proofs
