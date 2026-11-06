/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCWeightedTotalMass

/-! Uniformly varying weights give close cutoff total masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

theorem regularizedGMC_varyingWithDensity_univ_mass_diff_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (u : ℝ → BoundedContinuousFunction ℂ ℝ) (hu : ∀ r z, 0 ≤ u r z)
    (v : BoundedContinuousFunction ℂ ℝ) (hv : ∀ z, 0 ≤ v z)
    (hconv : TendstoUniformly (fun r z => u r z) v atTop) :
    TendstoInMeasure P
      (fun r ω =>
        (((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
        (((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (v z))) Set.univ).toReal)
      atTop (fun _ => 0) := by
  let μ : ℝ → Ω → Measure ℂ := fun r ω => regularizedGMC P Xc γ r ω
  let diff : ℝ → ℂ → ℝ := fun r z => |u r z - v z|
  let gap : ℝ → Ω → ℝ≥0∞ := fun r ω =>
    ∫⁻ z, ENNReal.ofReal (diff r z) ∂μ r ω
  let refMass := gmcReferenceMeasure Set.univ
  have hμMeas (r : ℝ) : Measurable (μ r) :=
    regularizedGMC_measurable P X hX Xc hXc γ r
  have hdiffMeas (r : ℝ) : Measurable (fun z : ℂ => ENNReal.ofReal (diff r z)) := by fun_prop
  have hgapMeas (r : ℝ) : Measurable (gap r) :=
    by fun_prop
  have hdiffBound (r : ℝ) z : diff r z ≤ ‖u r - v‖ := by
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
      have hz' : |u r z - v z| < ε / 2 := by
        simpa [Real.dist_eq, abs_sub_comm] using (hr z)
      exact le_of_lt hz'
    have hstrict : ε / 2 < ε := by linarith
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using (lt_of_le_of_lt hle hstrict)
  have hgapExpectation (r : ℝ) :
      ∫⁻ ω, gap r ω ∂P = ∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure := by
    dsimp [gap, diff, μ]
    exact regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r
      (fun z => ENNReal.ofReal |u r z - v z|) (hdiffMeas r)
  have hgapBound (r : ℝ) :
      ∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure ≤
        ENNReal.ofReal ‖u r - v‖ * refMass := by
    calc
      ∫⁻ z, ENNReal.ofReal (diff r z) ∂gmcReferenceMeasure ≤
          ∫⁻ z, ENNReal.ofReal ‖u r - v‖ ∂gmcReferenceMeasure := by
            apply lintegral_mono
            intro z
            exact ENNReal.ofReal_le_ofReal (hdiffBound r z)
      _ = ENNReal.ofReal ‖u r - v‖ * refMass := by aesop
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let den := ENNReal.ofReal ε
  have hden0 : den ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hdenTop : den ≠ ∞ := ENNReal.ofReal_ne_top
  have hrefTop : refMass ≠ ∞ := by simpa [refMass] using gmcReferenceMeasure_univ_ne_top
  have hprobT : Tendsto (fun r : ℝ =>
      (ENNReal.ofReal ‖u r - v‖ * refMass) / den) atTop (𝓝 0) := by
    have hmul' := ((ENNReal.continuous_mul_const hrefTop).tendsto
      (ENNReal.ofReal 0)).comp ((ENNReal.continuous_ofReal.tendsto 0).comp hnorm)
    change Tendsto (fun r : ℝ => ENNReal.ofReal ‖u r - v‖ * refMass) atTop
      (𝓝 _) at hmul'
    have hmul : Tendsto (fun r : ℝ => ENNReal.ofReal ‖u r - v‖ * refMass)
        atTop (𝓝 0) := by simp_all
    have hdiv' := ((ENNReal.continuous_div_const den hden0).tendsto 0).comp hmul
    change Tendsto (fun r : ℝ => ENNReal.ofReal ‖u r - v‖ * refMass / den) atTop
      (𝓝 _) at hdiv'
    simpa [zero_div] using hdiv'
  have hεevent (r : ℝ) : P {ω | ε ≤ |(
      (((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
      (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) Set.univ).toReal)|} ≤
      (ENNReal.ofReal ‖u r - v‖ * refMass) / den := by
    have hfinite : ∀ᵐ ω ∂P, IsFiniteMeasure (μ r ω) := by
      have hmass : ∫⁻ ω, (μ r ω) Set.univ ∂P = gmcReferenceMeasure Set.univ := by
        dsimp [μ]
        simpa using regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r
          (fun _ : ℂ => 1) measurable_const
      have htotalMeas : Measurable (fun ω => (μ r ω) Set.univ) :=
        (Measure.measurable_coe MeasurableSet.univ).comp (hμMeas r)
      have href : gmcReferenceMeasure Set.univ ≠ ∞ := gmcReferenceMeasure_univ_ne_top
      filter_upwards [ae_lt_top htotalMeas (by simp_all)] with ω hω
      exact ⟨hω⟩
    have hsub : ∀ᵐ ω ∂P,
        ε ≤ |(((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
            (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) Set.univ).toReal| →
          ENNReal.ofReal ε ≤ gap r ω := by
      filter_upwards [hfinite] with ω hμfin hω
      have hmemU :=
        @MemLp.of_bound ℂ ℝ _ 1 _ _ hμfin (u r)
          (u r).continuous.measurable.aestronglyMeasurable ‖u r‖
          (ae_of_all _ fun z => (u r).norm_coe_le_norm z)
      have hmemV :=
        @MemLp.of_bound ℂ ℝ _ 1 (μ r ω) _ hμfin v
          v.continuous.measurable.aestronglyMeasurable ‖v‖
          (ae_of_all _ fun z => v.norm_coe_le_norm z)
      have hdist := dist_integral_le_lintegral_edist
        (hmemU.integrable (by norm_num))
        (hmemV.integrable (by norm_num))
      have hmassEq :
          (((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
            (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) Set.univ).toReal =
          ∫ z, u r z ∂μ r ω - ∫ z, v z ∂μ r ω := by rw [(DOZZ.Proofs.weightedTotal_eq_integral (μ r ω) hμfin (u r) (hu r)), (DOZZ.Proofs.weightedTotal_eq_integral _ hμfin v hv)]
      rw [hmassEq] at hω
      have hgapEdist : ∫⁻ z, edist (u r z) (v z) ∂μ r ω = gap r ω := by
        apply lintegral_congr
        intro z
        simp [diff, edist_dist, Real.dist_eq]
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
      have hdist2 : dist (∫ z, u r z ∂μ r ω) (∫ z, v z ∂μ r ω) ≤
          (gap r ω).toReal := by
        calc
          dist _ _ ≤
              (∫⁻ z, edist _ (v z) ∂μ r ω).toReal := hdist
          _ = (gap r ω).toReal := by simp_all
      have hdist' : |(∫ z, u r z ∂μ r ω) - ∫ z, v z ∂μ r ω| ≤
          (gap r ω).toReal := by assumption
      exact (ENNReal.ofReal_le_iff_le_toReal hgapTop).2 (hω.trans hdist')
    have hmarkov : P {ω | ENNReal.ofReal ε ≤ gap r ω} ≤
        (∫⁻ ω, gap r ω ∂P) / den := by
      apply meas_ge_le_lintegral_div (hgapMeas r).aemeasurable
      · exact hden0
      · exact hdenTop
    calc
      P {ω | ε ≤ |(
          (((μ r ω).withDensity (fun z => ENNReal.ofReal _)) Set.univ).toReal -
          (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) Set.univ).toReal)|} ≤
          P {ω | ENNReal.ofReal ε ≤ gap r ω} := measure_mono_ae hsub
      _ ≤ (∫⁻ ω, gap r ω ∂P) / den := hmarkov
      _ = (∫⁻ z, ENNReal.ofReal _ ∂gmcReferenceMeasure) / den := by
          rw [hgapExpectation]
      _ ≤ (ENNReal.ofReal ‖u r - v‖ * refMass) / den := ENNReal.div_le_div_right (hgapBound r) den
  have hprob : Tendsto (fun r : ℝ => P {ω | ε ≤ |(
      (((μ r ω).withDensity (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal -
      (((μ r ω).withDensity (fun z => ENNReal.ofReal (v z))) Set.univ).toReal)|})
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hprobT
    · simp
    · simp_all
  simpa [μ, Real.norm_eq_abs] using hprob

end DOZZ.Proofs
