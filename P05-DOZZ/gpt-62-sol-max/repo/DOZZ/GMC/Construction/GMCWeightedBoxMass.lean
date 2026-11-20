module
public import DOZZ.GMC.Construction.GMCGeneralTiltBasisProxy
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.ConvergenceApproximation
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import DOZZ.GMC.Construction.ReferenceMeasureFinite

/-! Cutoff convergence on rational lower boxes, with or without a bounded weight. -/
@[expose] public section
open MeasureTheory Filter Topology Set
open scoped Distributions ENNReal NNReal BoundedContinuousFunction
namespace DOZZ.Proofs

private noncomputable abbrev boxIndicator (i : ℚ × ℚ) : ℂ → ℝ := (gmcLowerBox i).indicator 1
private noncomputable abbrev boxRampGap (i : ℚ × ℚ) (n : ℕ) : ℂ → ℝ≥0∞ :=
  fun z => edist (boxIndicator i z) (gmcLowerBoxApprox i n z)

section
variable (i : ℚ × ℚ)

private theorem measurable_boxIndicator : Measurable (boxIndicator i) :=
  measurable_const.indicator (gmcLowerBox_measurableSet i)

private theorem measurable_boxRampGap (n : ℕ) : Measurable (boxRampGap i n) :=
  (measurable_boxIndicator i).edist (gmcLowerBoxApprox i n).continuous.measurable

private theorem boxRampGap_le_one (n : ℕ) (z : ℂ) : boxRampGap i n z ≤ 1 := by
  rw [boxRampGap, edist_dist, Real.dist_eq, ENNReal.ofReal_le_one, abs_le]
  obtain ⟨h₀, h₁⟩ := gmcLowerBoxApprox_bounds i n z
  change 0 ≤ gmcLowerBoxApprox i n z at h₀
  change gmcLowerBoxApprox i n z ≤ 1 at h₁
  by_cases hz : z ∈ gmcLowerBox i <;> simp [boxIndicator, hz] <;>
    constructor <;> linarith

private theorem weightedBoxRampGap_tendsto (w : BoundedContinuousFunction ℂ ℝ) :
    Tendsto (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (w z) * boxRampGap i n z ∂gmcReferenceMeasure)
      atTop (𝓝 0) := by
  have hw := ENNReal.measurable_ofReal.comp w.continuous.measurable
  rw [← lintegral_zero (μ := gmcReferenceMeasure)]
  refine tendsto_lintegral_of_dominated_convergence (F := fun n z => ENNReal.ofReal (w z) * boxRampGap i n z)
    (fun _ => ENNReal.ofReal ‖w‖)
    (fun n => hw.mul (measurable_boxRampGap i n)) (fun n => ae_of_all _ fun z => ?_)
    (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top gmcReferenceMeasure_univ_ne_top)
    (ae_of_all _ fun z => ?_)
  · refine (mul_le_of_le_one_right' (boxRampGap_le_one i n z)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using w.norm_coe_le_norm z)
  · have h := (tendsto_const_nhds (x := boxIndicator i z)).edist (gmcLowerBoxApprox_tendsto i z)
    simp only [boxIndicator, Pi.one_def, edist_self] at h
    simpa only [boxRampGap, boxIndicator, Pi.one_def, mul_zero] using ENNReal.Tendsto.const_mul h (a := ENNReal.ofReal (w z)) (Or.inr ENNReal.ofReal_ne_top)

end

section
variable {Ω : Type*}

/-- Markov's bound with the exact expected cutoff intensity. -/
private theorem weightedBoxRamp_error [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) (i : ℚ × ℚ) (n : ℕ)
    (w : BoundedContinuousFunction ℂ ℝ) (ε : ℝ) (hε : 0 < ε) :
    let W := fun z => ENNReal.ofReal (w z)
    let ν := fun ω => (regularizedGMC P Xc γ r ω).withDensity W
    P {ω | ε ≤ dist (ν ω (gmcLowerBox i)).toReal (∫ z, gmcLowerBoxApprox i n z ∂ν ω)} ≤
      (∫⁻ z, W z * boxRampGap i n z ∂gmcReferenceMeasure) / ENNReal.ofReal ε := by
  intro W ν
  let φ := fun z => W z * boxRampGap i n z
  let gap := fun ω => ∫⁻ z, φ z ∂regularizedGMC P Xc γ r ω
  have hW : Measurable W := ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hφ : Measurable φ := hW.mul (measurable_boxRampGap i n)
  have hgap := (Measure.measurable_lintegral hφ).comp (regularizedGMC_measurable P X hX Xc hXc γ r)
  rw [← regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r φ hφ]
  refine (measure_mono_ae ?_).trans
    (meas_ge_le_lintegral_div hgap.aemeasurable (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top)
  filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω hdist
  letI := hω
  haveI : IsFiniteMeasure (ν ω) := isFiniteMeasure_withDensity_ofReal (w.integrable (μ := regularizedGMC P Xc γ r ω)).2
  have hi : Integrable (boxIndicator i) (ν ω) := (integrable_const (1 : ℝ)).indicator (gmcLowerBox_measurableSet i)
  have hg := edist_integral_le_lintegral_edist hi ((gmcLowerBoxApprox i n).integrable (μ := ν ω))
  rw [integral_indicator_one (gmcLowerBox_measurableSet i), edist_dist] at hg
  refine (ENNReal.ofReal_le_ofReal hdist).trans (hg.trans_eq ?_)
  exact lintegral_withDensity_eq_lintegral_mul _ hW (measurable_boxRampGap i n)

/-- The weighted cutoff box mass converges in measure to the weighted limit mass. -/
theorem regularizedGMC_withDensity_box_mass_tendstoInMeasure [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (w : BoundedContinuousFunction ℂ ℝ) (hw : ∀ z, 0 ≤ w z) (i : ℚ × ℚ) :
    TendstoInMeasure P
      (fun r ω => ((regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal (w z))
        (gmcLowerBox i)).toReal) atTop
      (fun ω => ((M ω).withDensity (fun z => ENNReal.ofReal (w z)) (gmcLowerBox i)).toReal) := by
  letI := hX.1
  let W := fun z => ENNReal.ofReal (w z)
  let νr := fun r ω => (regularizedGMC P Xc γ r ω).withDensity W
  let ν := fun ω => (M ω).withDensity W
  let A := fun n r ω => ∫ z, gmcLowerBoxApprox i n z ∂νr r ω
  let B := fun n ω => ∫ z, gmcLowerBoxApprox i n z ∂ν ω
  let L := fun ω => (ν ω (gmcLowerBox i)).toReal
  have hInt (μ : Measure ℂ) (f : BoundedContinuousFunction ℂ ℝ) :
      ∫ z, f z ∂μ.withDensity W = ∫ z, (w * f) z ∂μ := by
    have hmW : Measurable W := ENNReal.measurable_ofReal.comp w.continuous.measurable
    simp [integral_withDensity_eq_integral_toReal_smul hmW (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), W, ENNReal.toReal_ofReal (hw _), smul_eq_mul, BoundedContinuousFunction.mul_apply]
  have hm : equatorGFFRawDistributionSigma X ≤ mΩ :=
    (measurable_pi_iff.mpr fun g : TestFn => (hX.2 g).1).comap_le
  have hB : TendstoInMeasure P B atTop L := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      obtain ⟨g, hg, he⟩ := equatorGFF_GMC_testIntegral_raw_measurable_version_of_IsGMCOf
        P X hX γ M hM (w * gmcLowerBoxApprox i n)
      exact ((hg.mono hm le_rfl).aemeasurable.congr (he.symm.trans
        (ae_of_all _ fun ω => (hInt (M ω) _).symm))).aestronglyMeasurable
    · refine ae_of_all _ fun ω => ?_
      haveI := hM.1 ω
      haveI : IsFiniteMeasure (ν ω) := isFiniteMeasure_withDensity_ofReal (w.integrable (μ := M ω)).2
      exact gmcLowerBoxApprox_integral_tendsto i (ν ω)
  obtain ⟨Yc, hYc, hYlim⟩ := hM.2
  have hAB n : TendstoInMeasure P (A n) atTop (B n) := by
    refine (hYlim (w * gmcLowerBoxApprox i n)).congr (fun r => ?_)
      (ae_of_all _ fun ω => (hInt (M ω) _).symm)
    filter_upwards [regularizedGMC_ae_eq_of_circleAverage P X hX Xc Yc hXc hYc γ r] with ω hω
    dsimp only [A, νr]
    rw [hω, hInt]
  apply tendstoInMeasure_of_probApprox
  intro ε hε δ hδ
  have hε₀ : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have hn₁ := ENNReal.tendsto_nhds_zero.mp (weightedBoxRampGap_tendsto i w) (δ * ENNReal.ofReal ε)
    (ENNReal.mul_pos hδ.ne' hε₀)
  have hn₂ := ENNReal.tendsto_nhds_zero.mp (tendstoInMeasure_iff_dist.mp hB ε hε) δ hδ
  obtain ⟨n, h₁, h₂⟩ := (hn₁.and hn₂).exists
  exact ⟨A n, B n, hAB n, Eventually.of_forall fun r =>
    (weightedBoxRamp_error P X hX Xc hXc γ r i n w ε hε).trans
      ((ENNReal.div_le_iff hε₀ ENNReal.ofReal_ne_top).2 h₁), h₂⟩

/-- The unweighted limit is the special case of the constant weight one. -/
theorem regularizedGMC_box_mass_tendstoInMeasure [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (i : ℚ × ℚ) :
    TendstoInMeasure P (fun r ω => (regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal) atTop
      (fun ω => (M ω (gmcLowerBox i)).toReal) := by
  simpa using regularizedGMC_withDensity_box_mass_tendstoInMeasure P X hX Xc hXc γ M hM 1
    (fun _ => by simp) i

end

end DOZZ.Proofs
