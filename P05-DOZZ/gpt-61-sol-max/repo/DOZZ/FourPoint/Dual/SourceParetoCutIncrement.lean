/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceRadialMoments
public import DOZZ.FourPoint.ParetoENNReal
public import DOZZ.FourPoint.Reflected.ReflectionMomentInput
public import DOZZ.Brownian.Reflection.LastCut
import Mathlib.Tactic
/-! The signed Pareto estimate on the supplied field, chaos and reflection data. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- All random moment and measurability hypotheses of the Pareto product estimate are proved
from the supplied field/chaos and reflection data. Its two scalar factors are the actual leading
charge-shift moment and first-order freezing moment. -/
abbrev dual_source_pareto_cut_increment_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h p c : ℝ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h) (hp : 0 < p)
    (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1) :=
  letI := hX.1
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let A := fun ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let b := dual_radial_scale γ ν h Xc z
  have ha : 0 < a := div_pos (mul_pos (by norm_num) (sub_pos.mpr hα₁)) hγ
  have ha1 : a < 1 := by bound
  have h4 : 1 < 4/γ^2 := by field_simp <;> nlinarith
  have hr : ‖z‖^(1-ξ) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (norm_nonneg z) hz (sub_nonneg.mpr hξ1.le)
  have hAp := (dual_source_outerMass_positive_finite_ae P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ z hz0 hz1 hz hr).mono
      fun ω hω => ENNReal.toReal_pos hω.1.ne' hω.2.ne
  have hAm := (dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have hSm := twoSidedReflectionCutMass_aemeasurable P γ c B Z
      (conditionedPair_aemeasurable P B ν hData.1)
      hData.2.1.2.2.2.1 hData.2.1.2.2.2.2.1
  have hbm : AEMeasurable b P :=
    (((hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable.const_mul γ).sub aemeasurable_const).sub
      aemeasurable_const |>.exp
  have hbp (ω : Ω) : 0 < b ω := Real.exp_pos _
  have hmoment (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 4/γ^2) :
      (∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω ^q ∂P) < ⊤ :=
    (lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (twoSidedReflectionCutMass_le_mass γ c B Z ω) hq0).trans_lt
      (reflected_reflection_mass_moment_lt_top P γ α₁ q B Z hα₁ hData hq)
  ennreal_pareto_product_increment_error P P p a hp ha ha1 A b
    (twoSidedReflectionCutMass γ c B Z) hAp hbp hAm hbm hSm
    (dual_radial_scale_moment_finite P X hX γ hγ hγ₂ M hM Xc hc
          ν h a α₁ α₂ α₃ ξ (p+a) hh hξ hξ1 (add_pos hp ha).le z hz0 hz)
    (by
      simpa only [Real.rpow_one] using dual_radial_scale_moment_finite
          P X hX γ hγ hγ₂ M hM Xc hc ν h 1 α₁ α₂ α₃ ξ (p+1) hh hξ hξ1
            (by linarith only [hp]) z hz0 hz)
    (hmoment a ha.le (ha1.trans h4))
    (by
      simpa only [ENNReal.rpow_one] using hmoment 1 zero_le_one h4)

end DOZZ.Proofs
