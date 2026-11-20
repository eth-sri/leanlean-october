/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCWeightedBoxMass
public import DOZZ.GMC.Construction.ReferenceMeasureFinite
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! Comparison of cutoff chaos masses for uniformly convergent spatial weights. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

theorem regularizedGMC_varyingWithDensity_set_mass_diff_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (u : ℝ → BoundedContinuousFunction ℂ ℝ) (hu : ∀ r z, 0 ≤ u r z)
    (v : BoundedContinuousFunction ℂ ℝ) (hv : ∀ z, 0 ≤ v z)
    (hconv : TendstoUniformly (fun r z => u r z) v atTop)
    {S : Set ℂ} (hS : MeasurableSet S) :
    TendstoInMeasure P
      (fun r ω =>
        (((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (u r z))) S).toReal -
        (((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (v z))) S).toReal)
      atTop (fun _ => 0) := by
  let μ := regularizedGMC P Xc γ
  let C : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ‖u r - v‖
  let Z : ℝ → Ω → ℝ≥0∞ := fun r ω => μ r ω Set.univ
  have hZ (r : ℝ) : Measurable (Z r) :=
    (Measure.measurable_coe MeasurableSet.univ).comp
      (regularizedGMC_measurable P X hX Xc hXc γ r)
  have hEZ (r : ℝ) : ∫⁻ ω, Z r ω ∂P = gmcReferenceMeasure Set.univ := by
    simpa [Z, μ] using regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r
      (fun _ => 1) measurable_const
  have hC : Tendsto C atTop (𝓝 0) := by
    have hu' := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr hconv
    simpa [C, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hu'.sub (tendsto_const_nhds (x := v))).norm
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let d := ENNReal.ofReal ε
  have hd : d ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hlim : Tendsto (fun r => C r * gmcReferenceMeasure Set.univ / d) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, Function.comp_def] using ((ENNReal.continuous_div_const d hd).tendsto _).comp
      (((ENNReal.continuous_mul_const gmcReferenceMeasure_univ_ne_top).tendsto _).comp hC)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) ?_
  intro r
  simp only [sub_zero]
  calc
    _ ≤ P {ω | d ≤ C r * Z r ω} := by
      apply measure_mono_ae
      filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hfin hω
      have he (w : ℂ →ᵇ ℝ) (hw : ∀ z, 0 ≤ w z) :
          ((μ r ω).withDensity (fun z => ENNReal.ofReal (w z)) S).toReal =
            ∫ z in S, w z ∂μ r ω := by
        rw [withDensity_apply _ hS, integral_eq_lintegral_of_nonneg_ae
          (ae_of_all _ hw) w.continuous.measurable.aestronglyMeasurable]
      have hb := (u r - v).norm_integral_le_mul_norm ((μ r ω).restrict S)
      rw [BoundedContinuousFunction.coe_sub, Pi.sub_def, integral_sub ((u r).integrable _) (v.integrable _)] at hb
      have hω' : ε ≤ ‖(∫ z in S, u r z ∂μ r ω) - ∫ z in S, v z ∂μ r ω‖ := by
        change ε ≤ ‖((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z)) S).toReal -
          ((μ r ω).withDensity (fun z => ENNReal.ofReal (v z)) S).toReal‖ at hω
        rwa [he _ (hu r), he _ hv] at hω
      have hm : ((μ r ω).restrict S).real Set.univ ≤ (μ r ω).real Set.univ :=
        ENNReal.toReal_mono (measure_ne_top _ _) (Measure.restrict_le_self (s := S) (μ := μ r ω) _)
      have hb' := ENNReal.ofReal_le_ofReal ((hω'.trans hb).trans
        (mul_le_mul_of_nonneg_right hm (norm_nonneg (u r - v))))
      simpa [C, Z, d, Measure.real_def, ENNReal.ofReal_mul, ENNReal.ofReal_toReal,
        measure_ne_top, mul_comm] using hb'
    _ ≤ (∫⁻ ω, C r * Z r ω ∂P) / d :=
      meas_ge_le_lintegral_div (measurable_const.mul (hZ r)).aemeasurable hd ENNReal.ofReal_ne_top
    _ = _ := by rw [lintegral_const_mul _ (hZ r), hEZ]

end DOZZ.Proofs
