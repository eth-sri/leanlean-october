/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.RetainedRadialMoments
public import DOZZ.FourPoint.Reflected.ParetoNonnegativeMass
public import DOZZ.FourPoint.Reflected.ReflectionRealMoments
public import DOZZ.Brownian.Reflection.LastCut
import Mathlib.Tactic

/-! The retained Pareto estimate for any measurable reflection mass dominated by the full mass. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace DOZZ.Proofs

/-- The signed increment averaged over the independent Pareto maximum. -/
noncomputable def paretoMassIncrement {Ω : Type*} (a p : ℝ) (A S : Ω → ℝ≥0∞)
    (b : Ω → ℝ) (v : Ω × Ω) : ℝ :=
  ∫ w, ((A v.1).toReal + b v.1 * (S v.2).toReal * w)^(-p) - (A v.1).toReal^(-p)
    ∂paretoMeasure 1 a

/-- Weighted inverse moment of the retained mass as a real expectation. -/
noncomputable def weightedInverseMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℝ) (A : Ω → ℝ≥0∞) (b : Ω → ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (b ω) * (A ω)^(-q) ∂P).toReal

noncomputable def paretoLeadingCoefficient (a p : ℝ) : ℝ :=
  a * Real.Gamma (-a) * Real.Gamma (p+a) / Real.Gamma p

theorem fusion_retained_pareto_increment_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (β e α₁ α₂ α₃ ξ h p : ℝ) (hβ : β < Q γ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h) (hp : 0 < p)
    (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z) (S₀ : Ω → ℝ≥0∞)
    (hSm : AEMeasurable S₀ P) (hSle : ∀ ω, S₀ ω ≤ twoSidedReflectionMass γ B Z ω)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let A := fun ω => fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ
    let b := fusionRadialScale γ e ν h Xc z
    let E := paretoMassIncrement a p A S₀ b
    let L := weightedInverseMoment P (p+a) A (fun ω => (b ω)^a)
    let F := weightedInverseMoment P (p+1) A b
    Integrable E (P.prod P) ∧
      |(∫ v, E v ∂P.prod P) - paretoLeadingCoefficient a p *
        L * (∫⁻ ω, S₀ ω ^ a ∂P).toReal| ≤
      (a*p/(1-a)) * F * (∫⁻ ω, S₀ ω ∂P).toReal := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let A := fun ω => (fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ).toReal
  let b := fusionRadialScale γ e ν h Xc z
  let S := fun ω => (S₀ ω).toReal
  have hν : 0 < ν := sub_pos.mpr hα₁
  have ha : 0 < a := div_pos (mul_pos (by norm_num) hν) hγ
  have ha1 : a < 1 := by
    dsimp only [a]
    rw [div_lt_one hγ]
    linarith only [hreflect]
  have h4 : 1 < 4/γ^2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hγ)]
    nlinarith only [hγ,hγ₂]
  have hS_moment (q : ℝ) (hq : 0 ≤ q) (hq₄ : q < 4/γ^2) :
      Integrable (fun ω => (S ω)^q) P ∧
      (∫ ω, (S ω)^q ∂P) = (∫⁻ ω, S₀ ω ^ q ∂P).toReal := by
    have hm := hSm.pow_const q
    have hf := (lintegral_mono fun ω => ENNReal.rpow_le_rpow (hSle ω) hq).trans_lt
      (reflected_reflection_mass_moment_lt_top P γ α₁ q B Z hα₁ hData hq₄)
    exact ⟨by simpa only [S, ENNReal.toReal_rpow] using integrable_toReal_of_lintegral_ne_top hm hf.ne,
      by simpa only [S, ENNReal.toReal_rpow] using integral_toReal hm (ae_lt_top' hm hf.ne)⟩
  have hS1 := hS_moment 1 zero_le_one h4
  have hSa := hS_moment a ha.le (ha1.trans h4)
  have hSp : ∀ᵐ ω ∂P, 0 ≤ S ω := ae_of_all P fun _ => ENNReal.toReal_nonneg
  have hAm : AEMeasurable A P :=
    ((fusionOuterMass_measurable γ β α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).ennreal_toReal
  have hbm : AEMeasurable b P := fusionRadialScale_aemeasurable P X Xc hc γ e ν h z
  have hbp (ω : Ω) : 0 < b ω := fusionRadialScale_pos ..
  obtain ⟨_, _, _, hr1⟩ := retained_circle_window hz0 hz hh hξ.le hξ1.le
  have hAp : ∀ᵐ ω ∂P, 0 < A ω :=
    (fusionOuterMass_positive_finite_ae P X hX γ hγ hγ₂ M hM β α₁ α₂ α₃ ξ
      hβ hα₁ hα₂ hα₃ z hz0 hz1 hz hr1).mono
      fun _ hw => ENNReal.toReal_pos hw.1.ne' hw.2.ne
  have hsource0 := fusion_radial_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
    β e ν h a α₁ α₂ α₃ ξ (p+a) hh hξ hξ1 (add_pos hp ha).le z hz0 hz
  have hsource1 := fusion_radial_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
    β e ν h 1 α₁ α₂ α₃ ξ (p+1) hh hξ hξ1 (by linarith only [hp]) z hz0 hz
  have hw := hAp.mono fun ω hω => reflected_pareto_parameter_weights p a (A ω) (b ω) hω (hbp ω).le
  have hF0 := hsource0.1.congr (hw.mono fun _ hω => by
    simpa only [show -(p+a) = -p-a by ring] using hω.1.symm)
  have hF1 := (show Integrable (fun ω => b ω * (A ω)^(-(p+1))) P from
    by simpa only [Real.rpow_one] using hsource1.1).congr (hw.mono fun _ hω => by
      simpa only [show -(p+1) = -p-1 by ring] using hω.2.symm)
  have he0 : (∫ ω, (A ω)^(-p)*(b ω/A ω)^a ∂P) =
      (∫⁻ ω, ENNReal.ofReal ((b ω)^a)*
        fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^(-(p+a)) ∂P).toReal := by
    rw [integral_congr_ae (hAp.mono fun ω hω =>
      (reflected_pareto_parameter_weights p a (A ω) (b ω) hω (hbp ω).le).1)]
    simpa only [show -(p+a) = -p-a by ring] using hsource0.2
  have he1 : (∫ ω, (A ω)^(-p)*(b ω/A ω) ∂P) =
      (∫⁻ ω, ENNReal.ofReal (b ω)*
        fusionOuterMass γ β α₁ α₂ α₃ (M ω) z ξ ^(-(p+1)) ∂P).toReal := by
    rw [integral_congr_ae (hAp.mono fun ω hω =>
      (reflected_pareto_parameter_weights p a (A ω) (b ω) hω (hbp ω).le).2)]
    simpa only [Real.rpow_one,show -(p+1) = -p-1 by ring] using hsource1.2
  have hhpareto := reflected_pareto_product_increment_error_nonneg P P p a hp ha ha1 A b S
    hAp (ae_of_all P hbp) hSp hF0 hF1 hSa.1 (by simpa only [Real.rpow_one] using hS1.1)
    hAm hbm hSm.ennreal_toReal
  rw [he0,he1,hSa.2] at hhpareto
  have hS1eq : (∫ ω, S ω ∂P) = (∫⁻ ω, S₀ ω ∂P).toReal := by
    simpa only [Real.rpow_one,ENNReal.rpow_one] using hS1.2
  rw [hS1eq] at hhpareto
  exact hhpareto

end DOZZ.Proofs
