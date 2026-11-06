module
public import DOZZ.GMC.Construction.GMCBoxMassLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import DOZZ.GMC.Construction.ReferenceMeasureFinite
import Mathlib.Tactic

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
    have hs  := gmcLowerBox_measurableSet i
    fun_prop
  have hbound : ∀ n, ∀ᵐ z ∂gmcReferenceMeasure,
      gmcWeightedLowerBoxRampGapIntegrand i n w z ≤ ENNReal.ofReal ‖w‖ := by
    intro n
    filter_upwards [] with z
    have h := gmcLowerBoxApprox_bounds i n z
    have hpos : 0 ≤ gmcLowerBoxApprox i n z := h.1
    have hle : gmcLowerBoxApprox i n z ≤ 1 := h.2
    have hgap : |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z -
        gmcLowerBoxApprox i n z| ≤ 1 := by
      rw [abs_le]
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
      ENNReal.ofReal |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z -
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
      (|(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z - gmcLowerBoxApprox i n z| * w z))
      atTop (𝓝 0)
    have hfn := gmcLowerBoxApprox_tendsto i z
    let b  := (gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z
    have hdiff : Tendsto (fun n => b - gmcLowerBoxApprox i n z) atTop (𝓝 0) := by
      have hb : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
      have h := hb.sub hfn
      simpa [b] using h
    have hgap : Tendsto (fun n => |b - gmcLowerBoxApprox i n z|) atTop (𝓝 0) := by
      simpa using hdiff.abs
    have hprod : Tendsto (fun n => |b - gmcLowerBoxApprox i n z| * w z)
        atTop (𝓝 0) := by
      simpa using hgap.mul_const (w z)
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp hprod
    continuity
  simpa using tendsto_lintegral_of_dominated_convergence
    (fun _ : ℂ => ENNReal.ofReal ‖w‖) hmeas hbound hfinite hlim

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) (i : ℚ × ℚ) (n : ℕ) (w : BoundedContinuousFunction ℂ ℝ)

include Ω _inst1 P X hX Xc hXc γ r i n w in
/-- Exact cutoff intensity identifies the expected weighted ramp error with its reference
integral. -/
theorem regularizedGMC_weightedLowerBoxRamp_gap_expectation
     :
    ∫⁻ ω, ∫⁻ z,
      ENNReal.ofReal |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z -
        gmcLowerBoxApprox i n z|
      ∂(regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal (w z)) ∂P =
    ∫⁻ z, gmcWeightedLowerBoxRampGapIntegrand i n w z ∂gmcReferenceMeasure := by
  let W  := fun z => ENNReal.ofReal (w z)
  let φ  := fun z => ENNReal.ofReal
    |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z - gmcLowerBoxApprox i n z|
  have hW  := ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hφ : Measurable φ := by
    apply ENNReal.measurable_ofReal.comp
    have hs  := gmcLowerBox_measurableSet i
    fun_prop
  let μ  := fun ω => regularizedGMC P Xc γ r ω
  let ν  := fun ω => (μ ω).withDensity W
  have hμ  := regularizedGMC_measurable P X hX Xc hXc γ r
  have hν : Measurable ν := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hEval : (fun ω => ν ω A) =
        fun ω => ∫⁻ z, A.indicator W z ∂μ ω := by
      continuity
    rw [hEval]
    fun_prop (disch := positivity)
  let ψ  := fun z => W z * φ z
  have hψ  := hW.mul hφ
  calc
    ∫⁻ ω, ∫⁻ z, φ z ∂ν ω ∂P =
        ∫⁻ ω, ∫⁻ z, ψ z ∂μ ω ∂P := lintegral_congr fun ω => id (lintegral_withDensity_eq_lintegral_mul (μ ω) hW hφ)
    _ = ∫⁻ z, ψ z ∂gmcReferenceMeasure :=
          regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r ψ hψ
    _ = ∫⁻ z, gmcWeightedLowerBoxRampGapIntegrand i n w z ∂gmcReferenceMeasure := by
          apply lintegral_congr
          intro z
          dsimp [ψ, W, φ, gmcWeightedLowerBoxRampGapIntegrand]
          rw [ENNReal.ofReal_mul (abs_nonneg _)]
          simp [mul_comm]

include Ω _inst1 P X hX Xc hXc γ r i n w in
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
  let f : ℂ → ℝ := gmcLowerBoxApprox i n
  let ib  := B.indicator (fun _ => (1 : ℝ))
  let W  := fun z => ENNReal.ofReal (w z)
  let φ  := fun z => ENNReal.ofReal |ib z - f z|
  let μ  := fun ω => regularizedGMC P Xc γ r ω
  let ν  := fun ω => (μ ω).withDensity W
  let gap  := fun ω => ∫⁻ z, φ z ∂ν ω

  have hB : MeasurableSet B := gmcLowerBox_measurableSet i
  have hib : Measurable ib := measurable_const.indicator hB
  have hW  := ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hφ : Measurable φ := by
    fun_prop
  have hμ  := regularizedGMC_measurable P X hX Xc hXc γ r
  have hν : Measurable ν := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hEval : (fun ω => ν ω A) =
        fun ω => ∫⁻ z, A.indicator W z ∂μ ω := by
      continuity
    rw [hEval]
    fun_prop (disch := positivity)
  have hgapMeas  := (Measure.measurable_lintegral hφ).comp hν
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
        continuity
      _ = ∫⁻ z, W z ∂gmcReferenceMeasure := id (regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r W hW)
  have hmassMeas : Measurable (fun ω => ν ω Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp hν
  have hfinite : ∀ᵐ ω ∂P, IsFiniteMeasure (ν ω) := by
    filter_upwards [ae_lt_top hmassMeas (by rw [htotal]; exact hWtotal)] with ω hω
    exact ⟨hω⟩
  have hφBound : ∀ z, φ z ≤ 1 := by
    intro z
    have h := gmcLowerBoxApprox_bounds i n z
    have hpos : 0 ≤ f z := h.1
    have hle : f z ≤ 1 := h.2
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
    let κ  := ν ω
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
        · have h0 : 0 ≤ f z := h.1
          linarith
        · exact (h.2)
      exact @MemLp.of_bound ℂ ℝ _ 1 κ _ hfin f
        (gmcLowerBoxApprox i n).continuous.aestronglyMeasurable 1 hbd
    have hIbInt : ∫ z, ib z ∂κ = (κ B).toReal := id (integral_indicator_one hB)
    have hGapEq : ∫⁻ z, edist (ib z) (f z) ∂κ = gap ω := by
      apply lintegral_congr
      intro z
      simp [φ, edist_dist, Real.dist_eq, ib, f]
    have hdist : dist ((κ B).toReal) (∫ z, f z ∂κ) ≤ (gap ω).toReal := by
      rw [← hIbInt, ← hGapEq]
      exact dist_integral_le_lintegral_edist
        (hIbMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1))
        (hFMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1))
    have hdist' : |(κ B).toReal - ∫ z, f z ∂κ| ≤ (gap ω).toReal := hdist
    have hgapTop : gap ω ≠ ∞ := by
      apply ne_of_lt
      calc
        gap ω ≤ ∫⁻ z, (1 : ℝ≥0∞) ∂κ := by
          apply lintegral_mono
          exact hφBound
        _ = κ Set.univ := by simp
        _ < ∞ := lt_top_iff_ne_top.mpr (@measure_ne_top ℂ _ κ hfin Set.univ)
    have hεgap  := hω.trans hdist'
    exact (ENNReal.ofReal_le_iff_le_toReal hgapTop).2 hεgap
  have hgapExp  := id (regularizedGMC_weightedLowerBoxRamp_gap_expectation P X hX Xc hXc γ r i n w)
  have hMarkov : P {ω | ENNReal.ofReal ε ≤ gap ω} ≤
      (∫⁻ ω, gap ω ∂P) / ENNReal.ofReal ε := by
    apply meas_ge_le_lintegral_div hgapMeas.aemeasurable
    all_goals simp_all
  calc
    P {ω | ε ≤ |(ν ω B).toReal - ∫ z, f z ∂(ν ω)|} ≤
        P {ω | ENNReal.ofReal ε ≤ gap ω} := measure_mono_ae hEventSub
    _ ≤ (∫⁻ ω, gap ω ∂P) / ENNReal.ofReal ε := hMarkov
    _ = _ := by rw [hgapExp]

/-- For each fixed nonnegative bounded continuous weight, the weighted cutoff box mass converges
in measure to the weighted mass of any `IsGMCOf` limit. -/
theorem regularizedGMC_withDensity_box_mass_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
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
  let W  := fun z => ENNReal.ofReal (w z)
  let μr  := fun r ω => regularizedGMC P Xc γ r ω
  let νr  := fun r ω => (μr r ω).withDensity W
  let ν  := fun ω => (M ω).withDensity W
  have hW : Measurable W := ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hWlt (μ : Measure ℂ) : ∀ᵐ z ∂μ, W z < ∞ := by
    continuity
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
          finiteness
  have hWfinite (μ : Measure ℂ) (hμ : IsFiniteMeasure μ) : IsFiniteMeasure (μ.withDensity W) :=
    isFiniteMeasure_withDensity (hWint μ hμ)
  have hIntEq (μ : Measure ℂ) (f : BoundedContinuousFunction ℂ ℝ) :
      ∫ z, f z ∂μ.withDensity W = ∫ z, (w * f) z ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul hW (hWlt μ) f]
    continuity
  have heval  :=
    measurable_pi_iff.mpr (fun g => (hX.2 g).1)
  have hm0 : equatorGFFRawDistributionSigma X ≤ mΩ := heval.comap_le
  have hBaseTest : TendstoInMeasure P
      (fun n ω => ∫ z, gmcLowerBoxApprox i n z ∂ν ω) atTop
      (fun ω => (ν ω B).toReal) := by
    have hseq : ∀ n, ∃ g : Ω → ℝ,
        Measurable[equatorGFFRawDistributionSigma X] g ∧
        (fun ω => ∫ z, (w * gmcLowerBoxApprox i n) z ∂M ω) =ᵐ[P] g := by
      intro n
      exact equatorGFF_GMC_testIntegral_raw_measurable_version_of_IsGMCOf
        P X hX γ M hM (w * gmcLowerBoxApprox i n)
    choose g hgmeas hgae using hseq
    have hFmeas (n : ℕ) : AEMeasurable
        (fun ω => ∫ z, gmcLowerBoxApprox i n z ∂ν ω) P := by
      have hEq' : (fun ω => ∫ z, gmcLowerBoxApprox i n z ∂ν ω) =ᵐ[P] g n := by
        aesop
      have hq'  := (hgmeas n).mono hm0 le_rfl
      exact hq'.aemeasurable.congr hEq'.symm
    let gLim  := fun ω => limUnder atTop (fun n => g n ω)
    have hgLim : Measurable[equatorGFFRawDistributionSigma X] gLim := by
      let  := equatorGFFRawDistributionSigma X
      exact (StronglyMeasurable.limUnder (l := atTop)
        (fun n => (hgmeas n).stronglyMeasurable)).measurable
    have hAEproxy : ∀ᵐ ω ∂P, ∀ n,
        (∫ z, gmcLowerBoxApprox i n z ∂ν ω) = g n ω := by
      apply ae_all_iff.mpr
      intro n
      filter_upwards [hgae n] with ω hω
      continuity
    have hEq : (fun ω => (ν ω B).toReal) =ᵐ[P] gLim := by
      filter_upwards [hAEproxy] with ω hω
      have hfin  := hWfinite (M ω) (hM.1 ω)
      have hT : Tendsto (fun n => g n ω) atTop (𝓝 ((ν ω B).toReal)) := by
        have h := @gmcLowerBoxApprox_integral_tendsto i (ν ω) hfin
        exact Tendsto.congr' (Filter.Eventually.of_forall hω) h
      exact hT.limUnder_eq.symm
    have hGmeas : AEMeasurable (fun ω => (ν ω B).toReal) P := by
      have hg'  := hgLim.mono hm0 le_rfl
      exact hg'.aemeasurable.congr hEq.symm
    have hpoint : ∀ᵐ ω ∂P, Tendsto
        (fun n => ∫ z, gmcLowerBoxApprox i n z ∂ν ω) atTop
        (𝓝 ((ν ω B).toReal)) := by
      apply ae_of_all
      intro ω
      have hfin  := hWfinite (M ω) (hM.1 ω)
      exact @gmcLowerBoxApprox_integral_tendsto i (ν ω) hfin
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
        fun ω => ∫ z, (w * f) z ∂M ω := ae_of_all P (fun ω => hIntEq (M ω) f)
    exact TendstoInMeasure.congr (fun r => (hseqEq r).symm)
      hlimEq.symm (hYlim (w * f))
  have hεevent (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun r => P {ω | ε ≤ |(νr r ω B).toReal - (ν ω B).toReal|})
        atTop (𝓝 0) := by
    let ε₃  := ε / 3
    have hε₃ : 0 < ε₃ := by dsimp [ε₃]; positivity
    let den  := ENNReal.ofReal ε₃
    have hden0  := (ENNReal.ofReal_pos.mpr hε₃).ne'
    have hdenTop : den ≠ ∞ := ENNReal.ofReal_ne_top
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    let η  := min δ (1 : ℝ≥0∞)
    have hηpos : 0 < η := lt_min hδ one_pos
    let large  := η / 2
    let small  := large / 2
    have hlargepos : 0 < large := ENNReal.div_pos hηpos.ne' (by norm_num)
    have hsmallpos : 0 < small := ENNReal.div_pos hlargepos.ne' (by norm_num)
    have hhalf (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
      simp_all
    have hsmallAdd : small + small = large := by
      bound
    have hlargeAdd : large + large = η := hhalf η
    have hRefEventual  :=
      ENNReal.tendsto_nhds_zero.mp
        (gmcWeightedLowerBoxRamp_referenceGap_tendsto i w hw)
        (small * den) (by positivity)
    have hBaseEventTendsto  :=
      (tendstoInMeasure_iff_norm.mp hBaseTest) ε₃ hε₃
    have hBaseEventual  :=
      ENNReal.tendsto_nhds_zero.mp hBaseEventTendsto small hsmallpos
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hRefEventual.and hBaseEventual)
    let n := N
    have hnRef := (hN N le_rfl).1
    have hnBase := (hN N le_rfl).2
    have hratio  :=
      (ENNReal.div_le_iff hden0 hdenTop).2 hnRef
    have hcutError : ∀ r : ℝ,
        P {ω | ε₃ ≤ ‖(νr r ω B).toReal -
          ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖} ≤ small := by
      intro r
      have hbound := regularizedGMC_weightedLowerBoxApprox_error_le_reference
        P X hX Xc hXc γ r i n w ε₃ hε₃
      exact hbound.trans hratio
    have hBaseEvent  := hnBase
    have hmidEventTendsto  :=
      (tendstoInMeasure_iff_norm.mp (hConvTest (gmcLowerBoxApprox i n))) ε₃ hε₃
    have hmidEventual  :=
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
           ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) - (ν ω B).toReal‖) := htri₁.trans (add_le_add_right htri₂ _)
      have hsmall₁  := lt_of_not_ge h₁
      have hsmall₂  := lt_of_not_ge h₂
      have hsmall₃  := lt_of_not_ge h₃
      dsimp [ε₃] at hsmall₁ hsmall₂ hsmall₃
      have hsum :
          ‖(νr r ω B).toReal - ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖ +
            (‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) -
                (∫ z, gmcLowerBoxApprox i n z ∂ν ω)‖ +
              ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) - (ν ω B).toReal‖) <
            ε₃ + (ε₃ + ε₃) := by
        bound
      have hsplit : ε₃ + (ε₃ + ε₃) = ε := by dsimp [ε₃]; ring
      have hfinal : ‖(νr r ω B).toReal - (ν ω B).toReal‖ < ε := by
        bound
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
              (measure_union_le _ _).trans
                (add_le_add_right (measure_union_le _ _) _)
        _ ≤ small + (large + small) :=
              add_le_add (hcutError r) (add_le_add hr hBaseEvent)
    calc
      P {ω | ε ≤ ‖(νr r ω B).toReal - (ν ω B).toReal‖} ≤
          small + (large + small) := hMeasure
      _ = η := by
        calc
          small + (large + small) = (small + small) + large := by ac_rfl
          _ = large + large := by rw [hsmallAdd]
          _ = η := hlargeAdd
      _ ≤ δ := min_le_left δ 1
  rw [tendstoInMeasure_iff_norm]
  omega

end
end DOZZ.Proofs
