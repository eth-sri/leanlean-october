module
public import DOZZ.GMC.Construction.GMCBoxMassLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import DOZZ.GMC.Construction.ReferenceMeasureFinite

open MeasureTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

@[expose] public section

/-- The reference integrand for the error between a rational lower-box indicator and its ramp,
weighted by a nonnegative bounded continuous function. -/
noncomputable def gmcWeightedLowerBoxRampGapIntegrand
    (i : ℚ × ℚ) (n : ℕ) (w : BoundedContinuousFunction ℂ ℝ)
    (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (|(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z - gmcLowerBoxApprox i n z| * w z)

/-- The weighted reference expectation of the lower-box ramp error tends to zero. -/
theorem gmcWeightedLowerBoxRamp_referenceGap_tendsto
    (i : ℚ × ℚ) (w : BoundedContinuousFunction ℂ ℝ)
    (hw : ∀ z, 0 ≤ w z) :
    Tendsto (fun n => ∫⁻ z, gmcWeightedLowerBoxRampGapIntegrand i n w z
      ∂gmcReferenceMeasure) atTop (𝓝 0) := by
  have hmeas : ∀ n, Measurable (gmcWeightedLowerBoxRampGapIntegrand i n w) := by
    intro n
    apply ENNReal.measurable_ofReal.comp
    have hs := gmcLowerBox_measurableSet i
    fun_prop
  have hbound : ∀ n, ∀ᵐ z ∂gmcReferenceMeasure,
      gmcWeightedLowerBoxRampGapIntegrand i n w z ≤ ENNReal.ofReal ‖w‖ := by
    intro n
    filter_upwards [] with z
    have h := gmcLowerBoxApprox_bounds i n z
    have hpos : 0 ≤ gmcLowerBoxApprox i n z := by
      tauto
    have hle : gmcLowerBoxApprox i n z ≤ 1 := by
      tauto
    have hgap : |(gmcLowerBox i).indicator (fun _ => 1) z -
        gmcLowerBoxApprox i n z| ≤ 1 := by
      by_cases hz : z ∈ gmcLowerBox i
      · simp [Set.indicator, hz]
        grind
      · simp [Set.indicator, hz]
        grind
    have hwle : w z ≤ ‖w‖ := by
      calc
        w z = |w z| := (abs_of_nonneg (hw z)).symm
        _ = ‖w z‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖w‖ := w.norm_coe_le_norm z
    rw [gmcWeightedLowerBoxRampGapIntegrand, ENNReal.ofReal_mul (abs_nonneg _)]
    calc
      ENNReal.ofReal |(gmcLowerBox i).indicator (fun _ => 1) z -
          gmcLowerBoxApprox i n z| * ENNReal.ofReal (w z) ≤
        ENNReal.ofReal 1 * ENNReal.ofReal ‖w‖ :=
          mul_le_mul (ENNReal.ofReal_le_ofReal hgap) (ENNReal.ofReal_le_ofReal hwle)
            (by positivity) (by positivity)
      _ = ENNReal.ofReal ‖w‖ := by simp
  have hfinite : ∫⁻ z : ℂ, ENNReal.ofReal ‖w‖ ∂gmcReferenceMeasure ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top gmcReferenceMeasure_univ_ne_top
  have hlim : ∀ᵐ z ∂gmcReferenceMeasure,
      Tendsto (fun n => gmcWeightedLowerBoxRampGapIntegrand i n w z) atTop (𝓝 0) := by
    apply ae_of_all
    intro z
    change Tendsto (fun n => ENNReal.ofReal
      (|(gmcLowerBox i).indicator (fun _ => 1) z - gmcLowerBoxApprox i n z| * w z))
      atTop (𝓝 0)
    let b : ℝ := (gmcLowerBox i).indicator (fun _ => 1) z
    have hdiff : Tendsto (fun n => b - gmcLowerBoxApprox i n z) atTop (𝓝 0) := by
      have hb : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
      simpa [b] using (hb.sub (gmcLowerBoxApprox_tendsto i z))
    have hgap : Tendsto (fun n => |b - gmcLowerBoxApprox i n z|) atTop (𝓝 0) := by
      simpa using hdiff.abs
    have hprod : Tendsto (fun n => |b - gmcLowerBoxApprox i n z| * w z)
        atTop (𝓝 0) := by
      simpa using hgap.mul_const (w z)
    convert ((ENNReal.continuous_ofReal.tendsto 0).comp hprod) using 1
    · rfl
    · simp
  simpa using tendsto_lintegral_of_dominated_convergence
    (fun _ => ENNReal.ofReal ‖w‖) hmeas hbound hfinite hlim
section
variable {Ω : Type*}
section
variable [MeasurableSpace Ω] (P : Measure Ω)
section
variable (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) (i : ℚ × ℚ) (n : ℕ) (w : BoundedContinuousFunction ℂ ℝ)
include hX hXc

/-- Exact cutoff intensity identifies the expected weighted ramp error with its reference
integral. -/
theorem regularizedGMC_weightedLowerBoxRamp_gap_expectation
    :
    ∫⁻ ω, ∫⁻ z,
      ENNReal.ofReal |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z -
        gmcLowerBoxApprox i n z|
      ∂(regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal (w z)) ∂P =
    ∫⁻ z, gmcWeightedLowerBoxRampGapIntegrand i n w z ∂gmcReferenceMeasure := by
  let W : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (w z)
  let φ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal
    |(gmcLowerBox i).indicator (fun _ => 1) z - gmcLowerBoxApprox i n z|
  have hW := ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hφ : Measurable φ := by
    apply ENNReal.measurable_ofReal.comp
    have hs := gmcLowerBox_measurableSet i
    fun_prop
  let μ : Ω → Measure ℂ := fun ω => regularizedGMC P Xc γ r ω
  let ν : Ω → Measure ℂ := fun ω => (μ ω).withDensity W
  have hμ := regularizedGMC_measurable P X hX Xc hXc γ r
  have hν : Measurable ν := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hEval : (fun ω => ν ω A) =
        fun ω => ∫⁻ z, A.indicator W z ∂μ ω := by
      aesop
    rw [hEval]
    fun_prop
  let ψ : ℂ → ℝ≥0∞ := fun z => W z * φ z
  calc
    ∫⁻ ω, ∫⁻ z, φ z ∂ν ω ∂P =
        ∫⁻ ω, ∫⁻ z, ψ z ∂μ ω ∂P := by
          apply lintegral_congr
          intro ω
          dsimp [ψ, ν]
          exact lintegral_withDensity_eq_lintegral_mul (μ ω) hW hφ
    _ = ∫⁻ z, ψ z ∂gmcReferenceMeasure :=
          regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r ψ (hW.mul hφ)
    _ = ∫⁻ z, gmcWeightedLowerBoxRampGapIntegrand i n w z ∂gmcReferenceMeasure := by
          apply lintegral_congr
          intro z
          dsimp [ψ, W, φ, gmcWeightedLowerBoxRampGapIntegrand]
          rw [ENNReal.ofReal_mul (abs_nonneg _)]
          simp [mul_comm]

/-- Markov's inequality controls the weighted cutoff box-mass error by the weighted reference
ramp error. -/
theorem regularizedGMC_weightedLowerBoxApprox_error_le_reference
    (ε : ℝ) (hε : 0 < ε) :
    P {ω | ε ≤ |((regularizedGMC P Xc γ r ω).withDensity
      (fun z => ENNReal.ofReal (w z)) (gmcLowerBox i)).toReal -
      ∫ z, gmcLowerBoxApprox i n z ∂(regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (w z))|} ≤
      (∫⁻ z, gmcWeightedLowerBoxRampGapIntegrand i n w z ∂gmcReferenceMeasure) /
        ENNReal.ofReal ε := by
  let B := gmcLowerBox i
  let f := gmcLowerBoxApprox i n
  let ib : ℂ → ℝ := B.indicator (fun _ => 1)
  let W : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (w z)
  let φ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal |ib z - f z|
  let μ : Ω → Measure ℂ := fun ω => regularizedGMC P Xc γ r ω
  let ν : Ω → Measure ℂ := fun ω => (μ ω).withDensity W
  let gap : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, φ z ∂ν ω
  let _ := hX.1
  have hB : MeasurableSet B := by simpa [B] using gmcLowerBox_measurableSet i
  have hib : Measurable ib := measurable_const.indicator hB
  have hφ : Measurable φ := by
    fun_prop
  have hμ := regularizedGMC_measurable P X hX Xc hXc γ r
  have hν : Measurable ν := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hEval : (fun ω => ν ω A) =
        fun ω => ∫⁻ z, A.indicator W z ∂μ ω := by
      aesop
    rw [hEval]
    fun_prop
  have hWbound : ∀ z, W z ≤ ENNReal.ofReal ‖w‖ := by
    intro z
    apply ENNReal.ofReal_le_ofReal
    calc
      w z ≤ |w z| := le_abs_self _
      _ = ‖w z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖w‖ := w.norm_coe_le_norm z
  have hWtotal : ∫⁻ z, W z ∂gmcReferenceMeasure ≠ ∞ := by
    apply ne_of_lt
    calc
      ∫⁻ z, W z ∂gmcReferenceMeasure ≤
          ∫⁻ z, ENNReal.ofReal ‖w‖ ∂gmcReferenceMeasure := lintegral_mono hWbound
      _ < ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top)
  have htotal : ∫⁻ ω, ν ω Set.univ ∂P = ∫⁻ z, W z ∂gmcReferenceMeasure := by
    calc
      ∫⁻ ω, ν ω Set.univ ∂P = ∫⁻ ω, ∫⁻ z, W z ∂μ ω ∂P := by
        apply lintegral_congr
        intro ω
        simp [ν, μ, withDensity_apply]
      _ = ∫⁻ z, W z ∂gmcReferenceMeasure := by
        simpa [μ] using regularizedGMC_lintegral_test_eq_reference
          P X hX Xc hXc γ r W (ENNReal.measurable_ofReal.comp w.continuous.measurable)
  have hmassMeas : Measurable (fun ω => ν ω Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp hν
  have hfinite : ∀ᵐ ω ∂P, IsFiniteMeasure (ν ω) := by
    filter_upwards [ae_lt_top hmassMeas (by simp_all)] with ω hω
    exact ⟨hω⟩
  have hφBound : ∀ z, φ z ≤ 1 := by
    intro z
    have h := gmcLowerBoxApprox_bounds i n z
    have hpos : 0 ≤ f z := by tauto
    have hle : f z ≤ 1 := by tauto
    change ENNReal.ofReal |ib z - f z| ≤ 1
    rw [ENNReal.ofReal_le_one, abs_le]
    by_cases hz : z ∈ B
    · simp [ib, hz]
      grind
    · simp [ib, hz]
      grind
  have hEventSub : ∀ᵐ ω ∂P,
      ε ≤ |(ν ω B).toReal - ∫ z, f z ∂ν ω| → ENNReal.ofReal ε ≤ gap ω := by
    filter_upwards [hfinite] with ω hfin hω
    let κ : Measure ℂ := ν ω
    have hIbMem : MemLp ib 1 κ := by
      have hbd : ∀ᵐ z ∂κ, ‖ib z‖ ≤ 1 := by
        filter_upwards [] with z
        by_cases hz : z ∈ B <;> simp [ib, hz]
      exact @MemLp.of_bound ℂ ℝ _ 1 κ _ hfin ib hib.aestronglyMeasurable 1 hbd
    have hFMem : MemLp f 1 κ := by
      have hbd : ∀ᵐ z ∂κ, ‖f z‖ ≤ 1 := by
        filter_upwards [] with z
        have h := gmcLowerBoxApprox_bounds i n z
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have h0 : 0 ≤ f z := by simpa [f, gmcLowerBoxApprox] using h.1
          linarith
        · tauto
      exact @MemLp.of_bound ℂ ℝ _ 1 κ _ hfin f
        (gmcLowerBoxApprox i n).continuous.aestronglyMeasurable 1 hbd
    have hIbInt : ∫ z, ib z ∂κ = (κ B).toReal := by
      change ∫ z, B.indicator 1 z ∂κ = κ.real B
      exact integral_indicator_one hB
    have hGapEq : ∫⁻ z, edist (ib z) (f z) ∂κ = gap ω := by
      apply lintegral_congr
      intro z
      simp [φ, edist_dist, Real.dist_eq, ib, f]
    have hdist : dist ((κ B).toReal) (∫ z, f z ∂κ) ≤ (gap ω).toReal := by
      rw [← hIbInt, ← hGapEq]
      exact dist_integral_le_lintegral_edist
        (hIbMem.integrable (by norm_num))
        (hFMem.integrable (by norm_num))
    have hdist' : |(κ B).toReal - ∫ z, f z ∂κ| ≤ (gap ω).toReal := by
      simpa [Real.dist_eq] using hdist
    have hgapTop : gap ω ≠ ∞ := by
      apply ne_of_lt
      calc
        gap ω ≤ ∫⁻ z, 1 ∂κ := by
          apply lintegral_mono
          exact hφBound
        _ = κ Set.univ := by simp
        _ < ∞ := lt_top_iff_ne_top.mpr (@measure_ne_top ℂ _ κ hfin Set.univ)
    exact (ENNReal.ofReal_le_iff_le_toReal hgapTop).2 (hω.trans hdist')
  have hgapExp : ∫⁻ ω, gap ω ∂P =
      ∫⁻ z, gmcWeightedLowerBoxRampGapIntegrand i n w z ∂gmcReferenceMeasure := by
    simpa [gap, ν, μ, φ] using
      regularizedGMC_weightedLowerBoxRamp_gap_expectation
        P X hX Xc hXc γ r i n w
  have hMarkov : P {ω | ENNReal.ofReal ε ≤ gap ω} ≤
      (∫⁻ ω, gap ω ∂P) / ENNReal.ofReal ε := by
    apply meas_ge_le_lintegral_div ((Measure.measurable_lintegral hφ).comp hν).aemeasurable
    · positivity
    · exact ENNReal.ofReal_ne_top
  calc
    P {ω | ε ≤ |(ν ω B).toReal - ∫ z, f z ∂(ν ω)|} ≤
        P {ω | ENNReal.ofReal ε ≤ gap ω} := measure_mono_ae hEventSub
    _ ≤ (∫⁻ ω, gap ω ∂P) / ENNReal.ofReal ε := hMarkov
    _ = _ := by simp_all

end

end

/-- For each fixed nonnegative bounded continuous weight, the weighted cutoff box mass converges
in measure to the weighted mass of any `IsGMCOf` limit. -/
theorem regularizedGMC_withDensity_box_mass_tendstoInMeasure
    [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (w : BoundedContinuousFunction ℂ ℝ) (hw : ∀ z, 0 ≤ w z)
    (i : ℚ × ℚ) :
    TendstoInMeasure P
      (fun r ω => ((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (w z)) (gmcLowerBox i)).toReal) atTop
      (fun ω => ((M ω).withDensity
        (fun z => ENNReal.ofReal (w z)) (gmcLowerBox i)).toReal) := by
  let _ := hX.1
  let B := gmcLowerBox i
  let W : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (w z)
  let μr : ℝ → Ω → Measure ℂ := fun r ω => regularizedGMC P Xc γ r ω
  let νr : ℝ → Ω → Measure ℂ := fun r ω => (μr r ω).withDensity W
  let ν : Ω → Measure ℂ := fun ω => (M ω).withDensity W
  have hW : Measurable W := ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hWlt (μ : Measure ℂ) : ∀ᵐ z ∂μ, W z < ∞ := by
    aesop
  have hWbound : ∀ z, W z ≤ ENNReal.ofReal ‖w‖ := by
    intro z
    apply ENNReal.ofReal_le_ofReal
    calc
      w z = |w z| := (abs_of_nonneg (hw z)).symm
      _ = ‖w z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖w‖ := w.norm_coe_le_norm z
  have hWint (μ : Measure ℂ) (hμ : IsFiniteMeasure μ) :
      ∫⁻ z, W z ∂μ ≠ ∞ := by
    apply ne_of_lt
    calc
      ∫⁻ z, W z ∂μ ≤ ∫⁻ z, ENNReal.ofReal ‖w‖ ∂μ := lintegral_mono hWbound
      _ < ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lt_top_iff_ne_top.mpr (@measure_ne_top ℂ _ μ hμ Set.univ))
  have hWfinite (μ : Measure ℂ) (hμ : IsFiniteMeasure μ) : IsFiniteMeasure (μ.withDensity W) :=
    isFiniteMeasure_withDensity (hWint μ hμ)
  have hIntEq (μ : Measure ℂ) (f : BoundedContinuousFunction ℂ ℝ) :
      ∫ z, f z ∂μ.withDensity W = ∫ z, (w * f) z ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hW (hWlt μ) f]
    aesop
  have heval : Measurable (fun ω => fun g : TestFn => X ω g) :=
    measurable_pi_iff.mpr (fun g => (hX.2 g).1)
  have hm0 : equatorGFFRawDistributionSigma X ≤ mΩ := by
    dsimp [equatorGFFRawDistributionSigma]
    exact heval.comap_le
  have hBaseTest : TendstoInMeasure P
      (fun n ω => ∫ z, gmcLowerBoxApprox i n z ∂ν ω) atTop
      (fun ω => (ν ω B).toReal) := by
    have hseq : ∀ n, ∃ g : Ω → ℝ,
        Measurable[equatorGFFRawDistributionSigma X] g ∧
        (fun ω => ∫ z, (w * gmcLowerBoxApprox i n) z ∂M ω) =ᵐ[P] g := by
      intro n
      exact equatorGFF_GMC_testIntegral_raw_measurable_version_of_IsGMCOf
        P X hX γ M hM _
    choose g hgmeas hgae using hseq
    have hFmeas (n : ℕ) : AEMeasurable
        (fun ω => ∫ z, gmcLowerBoxApprox i n z ∂ν ω) P := by
      have hEq' : (fun ω => ∫ z, gmcLowerBoxApprox i n z ∂ν ω) =ᵐ[P] g n := by
        filter_upwards [hgae n] with ω hω
        change ∫ z, gmcLowerBoxApprox i n z ∂(M ω).withDensity W = g n ω
        rw [hIntEq]
        exact hω
      have hq' : Measurable (g n) := (hgmeas n).mono hm0 le_rfl
      exact hq'.aemeasurable.congr hEq'.symm
    let gLim : Ω → ℝ := fun ω => limUnder atTop (fun n => g n ω)
    have hgLim : Measurable[equatorGFFRawDistributionSigma X] gLim := by
      let : MeasurableSpace Ω := equatorGFFRawDistributionSigma X
      exact (StronglyMeasurable.limUnder (l := atTop)
        (fun n => (hgmeas n).stronglyMeasurable)).measurable
    have hAEproxy : ∀ᵐ ω ∂P, ∀ n,
        (∫ z, gmcLowerBoxApprox i n z ∂ν ω) = g n ω := by
      apply ae_all_iff.mpr
      intro n
      filter_upwards [hgae n] with ω hω
      change ∫ z, gmcLowerBoxApprox i n z ∂(M ω).withDensity W = g n ω
      rw [hIntEq]
      exact hω
    have hEq : (fun ω => (ν ω B).toReal) =ᵐ[P] gLim := by
      filter_upwards [hAEproxy] with ω hω
      have hfin : IsFiniteMeasure (ν ω) := hWfinite (M ω) (hM.1 ω)
      have hT : Tendsto (fun n => g n ω) atTop (𝓝 ((ν ω B).toReal)) := by
        exact Tendsto.congr' (Filter.Eventually.of_forall hω) (@gmcLowerBoxApprox_integral_tendsto i (ν ω) hfin)
      change (ν ω B).toReal = limUnder atTop (fun n => g n ω)
      exact hT.limUnder_eq.symm
    have hGmeas : AEMeasurable (fun ω => (ν ω B).toReal) P := by
      have hg' : Measurable gLim := hgLim.mono hm0 le_rfl
      exact hg'.aemeasurable.congr hEq.symm
    have hpoint : ∀ᵐ ω ∂P, Tendsto
        (fun n => ∫ z, gmcLowerBoxApprox i n z ∂ν ω) atTop
        (𝓝 ((ν ω B).toReal)) := by
      apply ae_of_all
      intro ω
      have hfin : IsFiniteMeasure (ν ω) := hWfinite (M ω) (hM.1 ω)
      simpa [Measure.real] using @gmcLowerBoxApprox_integral_tendsto i (ν ω) hfin
    exact tendstoInMeasure_of_tendsto_ae
      (fun n => (hFmeas n).aestronglyMeasurable) hpoint
  obtain ⟨Yc, hYc, hYlim⟩ := hM.2
  have hConvTest (f : BoundedContinuousFunction ℂ ℝ) :
      TendstoInMeasure P
        (fun r ω => ∫ z, f z ∂νr r ω) atTop
        (fun ω => ∫ z, f z ∂ν ω) := by
    have hcut (r : ℝ) :
        (fun ω => νr r ω) =ᵐ[P]
          fun ω => (regularizedGMC P Yc γ r ω).withDensity W := by
      filter_upwards [regularizedGMC_ae_eq_of_circleAverage
        P X hX Xc Yc hXc hYc γ r] with ω hω
      simp [νr, μr, hω]
    have hseqEq (r : ℝ) :
        (fun ω => ∫ z, f z ∂νr r ω) =ᵐ[P]
          fun ω => ∫ z, (w * f) z ∂regularizedGMC P Yc γ r ω := by
      filter_upwards [hcut r] with ω hω
      rw [hω, hIntEq]
    have hlimEq : (fun ω => ∫ z, f z ∂ν ω) =ᵐ[P]
        fun ω => ∫ z, (w * f) z ∂M ω := by
      exact ae_of_all P (fun ω => hIntEq (M ω) f)
    exact TendstoInMeasure.congr (fun r => (hseqEq r).symm)
      hlimEq.symm (hYlim _)
  have hεevent (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun r => P {ω | ε ≤ |(νr r ω B).toReal - (ν ω B).toReal|})
        atTop (𝓝 0) := by
    let ε₃ := ε / 3
    have hε₃ : 0 < ε₃ := by positivity
    let den := ENNReal.ofReal ε₃
    have hden0 : den ≠ 0 := (ENNReal.ofReal_pos.mpr hε₃).ne'
    have hdenTop : den ≠ ∞ := ENNReal.ofReal_ne_top
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    let η := min δ (1 : ℝ≥0∞)
    have hηpos : 0 < η := by positivity
    let large := η / 2
    let small := large / 2
    have hlargepos : 0 < large := by
      dsimp [large]
      exact ENNReal.div_pos hηpos.ne' (by norm_num)
    have hsmallpos : 0 < small := by
      exact ENNReal.div_pos hlargepos.ne' (by norm_num)
    have hhalf (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
      rw [ENNReal.div_add_div_same, ← two_mul, mul_comm]
      exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    have hsmallAdd : small + small = large := by
      exact hhalf _
    have hlargeAdd : large + large = η := by
      exact hhalf η
    have hRefEventual : ∀ᶠ n : ℕ in atTop,
        (∫⁻ z, gmcWeightedLowerBoxRampGapIntegrand i n w z ∂gmcReferenceMeasure) ≤
          small * den :=
      ENNReal.tendsto_nhds_zero.mp
        (gmcWeightedLowerBoxRamp_referenceGap_tendsto i w hw)
        (small * den) (by positivity)
    have hBaseEventTendsto : Tendsto
        (fun n => P {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) -
          (ν ω B).toReal‖}) atTop (𝓝 0) :=
      (tendstoInMeasure_iff_norm.mp hBaseTest) ε₃ hε₃
    have hBaseEventual : ∀ᶠ n : ℕ in atTop,
        P {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) -
          (ν ω B).toReal‖} ≤ small :=
      ENNReal.tendsto_nhds_zero.mp hBaseEventTendsto small hsmallpos
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hRefEventual.and hBaseEventual)
    let n := N
    have hratio :
        (∫⁻ z, gmcWeightedLowerBoxRampGapIntegrand i n w z ∂gmcReferenceMeasure) / den ≤ small :=
      (ENNReal.div_le_iff hden0 hdenTop).2 ((hN N le_rfl).1)
    have hcutError : ∀ r : ℝ,
        P {ω | ε₃ ≤ ‖(νr r ω B).toReal -
          ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖} ≤ small := by
      intro r
      have hbound := regularizedGMC_weightedLowerBoxApprox_error_le_reference
        P X hX Xc hXc γ r i n w ε₃ hε₃
      simpa [den, Real.norm_eq_abs] using hbound.trans hratio
    have hBaseEvent :
        P {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) -
          (ν ω B).toReal‖} ≤ small := ((hN N le_rfl).2)
    have hmidEventTendsto : Tendsto
        (fun r => P {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) -
          (∫ z, gmcLowerBoxApprox i n z ∂ν ω)‖}) atTop (𝓝 0) :=
      (tendstoInMeasure_iff_norm.mp (hConvTest (gmcLowerBoxApprox i n))) ε₃ hε₃
    have hmidEventual : ∀ᶠ r : ℝ in atTop,
        P {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) -
          (∫ z, gmcLowerBoxApprox i n z ∂ν ω)‖} ≤ large :=
      ENNReal.tendsto_nhds_zero.mp hmidEventTendsto large hlargepos
    have htri (r : ℝ) :
        {ω | ε ≤ ‖(νr r ω B).toReal - (ν ω B).toReal‖} ⊆
        {ω | ε₃ ≤ ‖(νr r ω B).toReal -
          ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖} ∪
        ({ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) -
          (∫ z, gmcLowerBoxApprox i n z ∂ν ω)‖} ∪
         {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) - (ν ω B).toReal‖}) := by
      intro ω hω
      by_contra hnot
      have h₁ : ¬ ε₃ ≤ ‖(νr r ω B).toReal -
          ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖ := by
        intro h
        exact hnot (Or.inl h)
      have h₂ : ¬ ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) -
          (∫ z, gmcLowerBoxApprox i n z ∂ν ω)‖ := by
        intro h
        exact hnot (Or.inr (Or.inl h))
      have h₃ : ¬ ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) - (ν ω B).toReal‖ := by
        intro h
        exact hnot (Or.inr (Or.inr h))
      have htri₁ := abs_sub_le ((νr r ω B).toReal)
        (∫ z, gmcLowerBoxApprox i n z ∂νr r ω) ((ν ω B).toReal)
      have htri₂ := abs_sub_le
        (∫ z, gmcLowerBoxApprox i n z ∂νr r ω)
        (∫ z, gmcLowerBoxApprox i n z ∂ν ω) ((ν ω B).toReal)
      have htri' : ‖(νr r ω B).toReal - (ν ω B).toReal‖ ≤
          ‖(νr r ω B).toReal - ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖ +
          (‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) -
            (∫ z, gmcLowerBoxApprox i n z ∂ν ω)‖ +
           ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) - (ν ω B).toReal‖) := by
        simpa [Real.norm_eq_abs] using htri₁.trans (add_le_add_right htri₂ _)
      have hsmall₁ : ‖(νr r ω B).toReal -
          ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖ < ε₃ := lt_of_not_ge h₁
      have hsmall₂ : ‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) -
          (∫ z, gmcLowerBoxApprox i n z ∂ν ω)‖ < ε₃ := lt_of_not_ge h₂
      have hsmall₃ : ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) -
          (ν ω B).toReal‖ < ε₃ := lt_of_not_ge h₃
      have hsum :
          ‖(νr r ω B).toReal - ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖ +
            (‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) -
                (∫ z, gmcLowerBoxApprox i n z ∂ν ω)‖ +
              ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) - (ν ω B).toReal‖) <
            ε₃ + (ε₃ + ε₃) := by
        exact add_lt_add hsmall₁ (add_lt_add hsmall₂ hsmall₃)
      have hsplit : ε₃ + (ε₃ + ε₃) = ε := by ring
      have hfinal : ‖(νr r ω B).toReal - (ν ω B).toReal‖ < ε := by
        rw [← hsplit]
        exact lt_of_le_of_lt htri' hsum
      change ε ≤ ‖(νr r ω B).toReal - (ν ω B).toReal‖ at hω
      exact (not_lt_of_ge hω) hfinal
    filter_upwards [hmidEventual] with r hr
    have hMeasure :
        P {ω | ε ≤ ‖(νr r ω B).toReal - (ν ω B).toReal‖} ≤ small + (large + small) := by
      calc
        _ ≤ P ({ω | ε₃ ≤ ‖(νr r ω B).toReal -
            ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖} ∪
          ({ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) -
            (∫ z, gmcLowerBoxApprox i n z ∂ν ω)‖} ∪
           {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) - (ν ω B).toReal‖})) :=
              measure_mono (htri r)
        _ ≤ P {ω | ε₃ ≤ ‖(νr r ω B).toReal -
            ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖} +
            (P {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) -
              (∫ z, gmcLowerBoxApprox i n z ∂ν ω)‖} +
             P {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) -
              (ν ω B).toReal‖}) :=
              (measure_union_le ..).trans
                (add_le_add_right (measure_union_le ..) _)
        _ ≤ small + (large + small) :=
              add_le_add (hcutError r) (add_le_add hr hBaseEvent)
    calc
      P {ω | ε ≤ ‖(νr r ω B).toReal - (ν ω B).toReal‖} ≤
          small + (large + small) := hMeasure
      _ = η := by
        calc
          small + (large + small) = (small + small) + large := by ac_rfl
          _ = large + large := by tauto
          _ = η := hlargeAdd
      _ ≤ δ := by grind
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simpa [Real.norm_eq_abs] using hεevent ε hε

end

end
end DOZZ.Proofs
