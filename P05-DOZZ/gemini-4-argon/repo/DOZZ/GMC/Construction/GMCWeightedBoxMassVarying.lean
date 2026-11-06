/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCWeightedBoxMass
public import DOZZ.GMC.Construction.ReferenceMeasureFinite

/-! Comparison of cutoff chaos masses for uniformly convergent spatial weights. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs



/-- The cutoff box masses from uniformly convergent nonnegative weights become close in
probability. The estimate is the exact cutoff-intensity bound for the integral of the absolute
weight difference. -/
theorem regularizedGMC_varyingWithDensity_box_mass_diff_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (u : ℝ → BoundedContinuousFunction ℂ ℝ) (hu : ∀ r z, 0 ≤ u r z)
    (v : BoundedContinuousFunction ℂ ℝ) (hv : ∀ z, 0 ≤ v z)
    (hconv : TendstoUniformly (fun r z => u r z) v atTop) (i : ℚ × ℚ) :
    TendstoInMeasure P
      (fun r ω =>
        (((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (u r z))) (gmcLowerBox i)).toReal -
        (((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (v z))) (gmcLowerBox i)).toReal)
      atTop (fun _ => 0) := by
  have regularizedGMC_withDensity_box_mass_eq_indicator_integral r (i : ℚ × ℚ) (w : BoundedContinuousFunction ℂ ℝ) (hw : ∀ z, 0 ≤ w z) ω (hfin : IsFiniteMeasure (regularizedGMC P Xc γ r ω)) : (((regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal (w z))) (gmcLowerBox i)).toReal = ∫ z, (gmcLowerBox i).indicator w z ∂regularizedGMC P Xc γ r ω := by
    let μ := regularizedGMC P Xc γ r ω
    let W : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (w z)
    have hW : Measurable W := ENNReal.measurable_ofReal.comp w.continuous.measurable
    have hWlt : ∀ᵐ z ∂μ, W z < ∞ := ae_of_all _ (fun z => ENNReal.ofReal_lt_top)
    have hEq : ∫ z, (gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z
        ∂μ.withDensity W = ∫ z, (gmcLowerBox i).indicator w z ∂μ := by
      rw [(integral_withDensity_eq_integral_toReal_smul hW hWlt ((gmcLowerBox i).indicator (fun _ : ℂ => (1 : ℝ))))]
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ gmcLowerBox i
      · simp [W, Set.indicator, hz, ENNReal.toReal_ofReal (hw z), smul_eq_mul]
      · simp [Set.indicator, hz]
    calc
      ((μ.withDensity W) (gmcLowerBox i)).toReal =
          ∫ z, (gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z ∂μ.withDensity W := (show ∫ z, (gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z ∂μ.withDensity W = ((μ.withDensity W) (gmcLowerBox i)).toReal by change ∫ z, (gmcLowerBox i).indicator 1 z ∂μ.withDensity W = (μ.withDensity W).real (gmcLowerBox i); exact integral_indicator_one (gmcLowerBox_measurableSet i)).symm
      _ = ∫ z, (gmcLowerBox i).indicator w z ∂μ := hEq
  have regularizedGMC_varyingWeight_gap_measurable (r : ℝ) (u : BoundedContinuousFunction ℂ ℝ) (v : BoundedContinuousFunction ℂ ℝ) := (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (u.continuous.measurable.sub v.continuous.measurable)))).comp (regularizedGMC_measurable P X hX Xc hXc γ r)
  let B := gmcLowerBox i
  let μ : ℝ → Ω → Measure ℂ := fun r ω => regularizedGMC P Xc γ r ω
  let diff : ℝ → ℂ → ℝ := fun r z => |u r z - v z|
  let gap : ℝ → Ω → ℝ≥0∞ := fun r ω => ∫⁻ z,
    ENNReal.ofReal (diff r z) ∂μ r ω
  let refMass := gmcReferenceMeasure Set.univ
  have hμMeas (r : ℝ) := regularizedGMC_measurable P X hX Xc hXc γ r
  have hgapMeas (r : ℝ) := regularizedGMC_varyingWeight_gap_measurable r (u r) v
  have hdiffBound (r : ℝ) (z : ℂ) : diff r z ≤ ‖u r - v‖ := by
    dsimp [diff]
    calc
      |u r z - v z| = ‖(u r - v) z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖u r - v‖ := (u r - v).norm_coe_le_norm z
  have hnorm : Tendsto (fun r : ℝ => ‖u r - v‖) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have huni := (Metric.tendstoUniformly_iff.mp hconv) (ε / 2) (by linarith)
    filter_upwards [huni] with r hr
    have hle : ‖u r - v‖ ≤ ε / 2 := by
      apply (BoundedContinuousFunction.norm_le (by linarith)).2
      intro z
      rw [Real.norm_eq_abs]
      exact le_of_lt (by simpa [Real.dist_eq, abs_sub_comm] using (hr z))
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using (lt_of_le_of_lt hle (show ε / 2 < ε by linarith))
  have hgapExpectation (r : ℝ) :
      ∫⁻ ω, gap r ω ∂P = ∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure := by
    dsimp [gap, diff, μ]
    exact regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r
      (fun z => ENNReal.ofReal |u r z - v z|)
      (ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp
          ((u r).continuous.measurable.sub v.continuous.measurable)))
  have hgapBound (r : ℝ) :
      ∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure ≤
        ENNReal.ofReal ‖u r - v‖ * refMass := by
    calc
      ∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure ≤
          ∫⁻ z, ENNReal.ofReal ‖u r - v‖ ∂gmcReferenceMeasure := by
            apply lintegral_mono
            intro z
            exact ENNReal.ofReal_le_ofReal (hdiffBound r z)
      _ = ENNReal.ofReal ‖u r - v‖ * refMass := by
            rw [lintegral_const]
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let den := ENNReal.ofReal ε
  have hden0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hdenTop : den ≠ ∞ := ENNReal.ofReal_ne_top
  have hrefTop : refMass ≠ ∞ := by
    simpa [refMass] using gmcReferenceMeasure_univ_ne_top
  have hprobT : Tendsto (fun r : ℝ =>
      (ENNReal.ofReal ‖u r - v‖ * refMass) / den) atTop (𝓝 0) := by
    have hOf := (ENNReal.continuous_ofReal.tendsto 0).comp hnorm
    have hmul' := ((ENNReal.continuous_mul_const hrefTop).tendsto
      (ENNReal.ofReal 0)).comp hOf
    change Tendsto (fun r : ℝ => ENNReal.ofReal ‖u r - v‖ * refMass) atTop
      (𝓝 (ENNReal.ofReal 0 * refMass)) at hmul'
    have hmul : Tendsto (fun r : ℝ => ENNReal.ofReal ‖u r - v‖ * refMass)
        atTop (𝓝 0) := by simpa using hmul'
    have hdiv := (ENNReal.continuous_div_const den hden0).tendsto 0
    have hdiv' := hdiv.comp hmul
    change Tendsto (fun r : ℝ => ENNReal.ofReal ‖u r - v‖ * refMass / den) atTop
      (𝓝 (0 / den)) at hdiv'
    simpa [zero_div] using hdiv'
  have hεevent : ∀ r : ℝ,
      P {ω | ε ≤ |(((μ r ω).withDensity
        (fun z => ENNReal.ofReal (u r z))) B).toReal -
        (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) B).toReal|} ≤
        (ENNReal.ofReal ‖u r - v‖ * refMass) / den := by
    intro r
    have hfinite : ∀ᵐ ω ∂P, IsFiniteMeasure (μ r ω) := by
      have hmass : ∫⁻ ω, (μ r ω) Set.univ ∂P = gmcReferenceMeasure Set.univ := by
        dsimp [μ]
        simpa using regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r
          (fun _ : ℂ => (1 : ℝ≥0∞)) measurable_const
      have hm : Measurable (fun ω => (μ r ω) Set.univ) :=
        (Measure.measurable_coe MeasurableSet.univ).comp (hμMeas r)
      have href : gmcReferenceMeasure Set.univ ≠ ∞ := gmcReferenceMeasure_univ_ne_top
      filter_upwards [ae_lt_top hm (by rw [hmass]; exact href)] with ω hω
      exact ⟨hω⟩
    have hsub : ∀ᵐ ω ∂P,
        ε ≤ |(((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) B).toReal -
            (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) B).toReal| →
          ENNReal.ofReal ε ≤ gap r ω := by
      filter_upwards [hfinite] with ω hμfin hω
      let fU := B.indicator (u r)
      let fV := B.indicator v
      have hUbd : ∀ᵐ z ∂μ r ω, ‖fU z‖ ≤ ‖u r‖ := by
        filter_upwards [] with z
        by_cases hz : z ∈ B
        · simpa [fU, hz, Real.norm_eq_abs] using (u r).norm_coe_le_norm z
        · simp [fU, hz]
      have hVbd : ∀ᵐ z ∂μ r ω, ‖fV z‖ ≤ ‖v‖ := by
        filter_upwards [] with z
        by_cases hz : z ∈ B
        · simpa [fV, hz, Real.norm_eq_abs] using v.norm_coe_le_norm z
        · simp [fV, hz]
      have hdist := dist_integral_le_lintegral_edist
        ((@MemLp.of_bound ℂ ℝ _ 1 (μ r ω) _ hμfin fU ((u r).continuous.measurable.indicator (gmcLowerBox_measurableSet i)).aestronglyMeasurable ‖u r‖ hUbd).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1))
        ((@MemLp.of_bound ℂ ℝ _ 1 (μ r ω) _ hμfin fV (v.continuous.measurable.indicator (gmcLowerBox_measurableSet i)).aestronglyMeasurable ‖v‖ hVbd).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1))
      rw [(show (((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) B).toReal - (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) B).toReal = ∫ z, fU z ∂μ r ω - ∫ z, fV z ∂μ r ω by rw [(regularizedGMC_withDensity_box_mass_eq_indicator_integral r i (u r) (hu r) ω hμfin), (regularizedGMC_withDensity_box_mass_eq_indicator_integral r i v hv ω hμfin)])] at hω
      have hgap : ∫⁻ z, edist (fU z) (fV z) ∂μ r ω ≤ gap r ω := by
        apply lintegral_mono
        intro z
        by_cases hz : z ∈ B
        · change edist (fU z) (fV z) ≤ ENNReal.ofReal (diff r z)
          rw [(show edist (fU z) (fV z) = ENNReal.ofReal (diff r z) by simp [fU, fV, hz, edist_dist, Real.dist_eq, diff])]
        · simp [fU, fV, hz]
      have hgapTop : gap r ω ≠ ∞ := by
        apply ne_of_lt
        calc
          gap r ω ≤ ∫⁻ z, ENNReal.ofReal ‖u r - v‖ ∂μ r ω := by
            apply lintegral_mono
            intro z
            exact ENNReal.ofReal_le_ofReal (hdiffBound r z)
          _ < ∞ := by
            rw [lintegral_const]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (lt_top_iff_ne_top.mpr (@measure_ne_top ℂ _ (μ r ω) hμfin Set.univ))
      have hdist2 : dist (∫ z, fU z ∂μ r ω) (∫ z, fV z ∂μ r ω) ≤
          (gap r ω).toReal := by
        calc
          dist (∫ z, fU z ∂μ r ω) (∫ z, fV z ∂μ r ω) ≤
              (∫⁻ z, edist (fU z) (fV z) ∂μ r ω).toReal := hdist
          _ ≤ (gap r ω).toReal := ENNReal.toReal_mono hgapTop hgap
      have hεgap := hω.trans (by simpa [Real.dist_eq] using hdist2)
      exact (ENNReal.ofReal_le_iff_le_toReal hgapTop).2 hεgap
    have hmarkov : P {ω | ENNReal.ofReal ε ≤ gap r ω} ≤
        (∫⁻ ω, gap r ω ∂P) / den := by
      apply meas_ge_le_lintegral_div (hgapMeas r).aemeasurable
      · exact hden0
      · exact hdenTop
    calc
      P {ω | ε ≤ |(((μ r ω).withDensity
          (fun z => ENNReal.ofReal (u r z))) B).toReal -
          (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) B).toReal|} ≤
          P {ω | ENNReal.ofReal ε ≤ gap r ω} := measure_mono_ae hsub
      _ ≤ (∫⁻ ω, gap r ω ∂P) / den := hmarkov
      _ = (∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure) / den := by
          rw [hgapExpectation]
      _ ≤ (ENNReal.ofReal ‖u r - v‖ * refMass) / den := by
          exact ENNReal.div_le_div_right (hgapBound r) den
  have hprob : Tendsto (fun r : ℝ => P {ω | ε ≤ |(
      (((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) B).toReal -
      (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) B).toReal)|})
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) atTop (𝓝 0)) hprobT
    · exact Filter.Eventually.of_forall (fun r => bot_le)
    · exact Filter.Eventually.of_forall hεevent
  simpa [μ, B, Real.norm_eq_abs] using hprob

end DOZZ.Proofs
