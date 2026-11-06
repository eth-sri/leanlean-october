module
public import DOZZ.GMC.Construction.GMCGeneralTiltBasisProxy
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import DOZZ.GMC.Construction.ReferenceMeasureFinite
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

public section

noncomputable def gmcLowerBoxApproxGapIntegrand (i : ℚ × ℚ) (n : ℕ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z - gmcLowerBoxApprox i n z|

/-- The reference expectation of the absolute error between a lower-box indicator and its
continuous ramp tends to zero. -/
theorem gmcLowerBoxApprox_referenceGap_tendsto (i : ℚ × ℚ) :
    Tendsto (fun n => ∫⁻ z, gmcLowerBoxApproxGapIntegrand i n z
      ∂gmcReferenceMeasure) atTop (𝓝 0) := by
  have hmeas : ∀ n, Measurable (gmcLowerBoxApproxGapIntegrand i n) := by
    intro n
    apply ENNReal.measurable_ofReal.comp
    have hs  := gmcLowerBox_measurableSet i
    fun_prop
  have hbound : ∀ n, ∀ᵐ z ∂gmcReferenceMeasure,
      gmcLowerBoxApproxGapIntegrand i n z ≤ 1 := by
    intro n
    filter_upwards [] with z
    have h := gmcLowerBoxApprox_bounds i n z
    have hpos : 0 ≤ (gmcLowerBoxApprox i n) z := h.1
    have hle : (gmcLowerBoxApprox i n) z ≤ 1 := h.2
    change ENNReal.ofReal
      |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z - (gmcLowerBoxApprox i n) z| ≤ 1
    rw [ENNReal.ofReal_le_one, abs_le]
    by_cases hz : z ∈ gmcLowerBox i
    · simp [Set.indicator, hz]
      grind
    · simp [Set.indicator, hz]
      grind
  have hfinite : ∫⁻ z : ℂ, (1 : ℝ≥0∞) ∂gmcReferenceMeasure ≠ ∞ := by
    simpa using gmcReferenceMeasure_univ_ne_top
  have hlim : ∀ᵐ z ∂gmcReferenceMeasure,
      Tendsto (fun n => gmcLowerBoxApproxGapIntegrand i n z) atTop (𝓝 0) := by
    apply ae_of_all
    intro z
    change Tendsto (fun n => ENNReal.ofReal
      |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z -
        gmcLowerBoxApprox i n z|) atTop (𝓝 0)
    have hfn := gmcLowerBoxApprox_tendsto i z
    let c  := (gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z
    have hdiff : Tendsto (fun n => c - (gmcLowerBoxApprox i n) z) atTop (𝓝 0) := by
      have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
      have h := hc.sub hfn
      simpa [c] using h
    have habs : Tendsto (fun n => |c - (gmcLowerBoxApprox i n) z|) atTop (𝓝 0) := by
      simpa using hdiff.abs
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp habs
    continuity
  simpa using tendsto_lintegral_of_dominated_convergence
    (fun _ : ℂ => (1 : ℝ≥0∞)) hmeas hbound hfinite hlim

/-- Markov's inequality bounds the cutoff discrepancy from a lower-box ramp by its exact
reference expectation. -/
theorem regularizedGMC_lowerBoxApprox_error_le_reference
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (i : ℚ × ℚ) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    P {ω | ε ≤ |(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
      ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω|} ≤
      (∫⁻ z, gmcLowerBoxApproxGapIntegrand i n z ∂gmcReferenceMeasure) /
        ENNReal.ofReal ε := by
  let B := gmcLowerBox i
  let f : ℂ → ℝ := gmcLowerBoxApprox i n
  let ib  := B.indicator (fun _ => (1 : ℝ))
  let φ  := fun z => ENNReal.ofReal |ib z - f z|
  let gap  := fun ω => ∫⁻ z, φ z ∂regularizedGMC P Xc γ r ω

  have hB : MeasurableSet B := gmcLowerBox_measurableSet i
  have hib : Measurable ib := measurable_const.indicator hB
  have hφ : Measurable φ := by
    fun_prop
  have hμ  :=
    regularizedGMC_measurable P X hX Xc hXc γ r
  have hgapMeas  :=
    (Measure.measurable_lintegral hφ).comp hμ
  have hgapExp : ∫⁻ ω, gap ω ∂P = ∫⁻ z, φ z ∂gmcReferenceMeasure := id (regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r φ hφ)
  have hphiBound : ∀ z, φ z ≤ 1 := by
    intro z
    have h := gmcLowerBoxApprox_bounds i n z
    have hpos : 0 ≤ f z := h.1
    have hle : f z ≤ 1 := h.2
    change ENNReal.ofReal |ib z - f z| ≤ 1
    rw [ENNReal.ofReal_le_one, abs_le]
    by_cases hz : z ∈ B
    · simp [ib, hz]
      constructor <;> linarith
    · simp [ib, hz]
      constructor <;> linarith
  have hfinite  :=
    regularizedGMC_finite_ae P X hX Xc hXc γ r
  have hEventSub : ∀ᵐ ω ∂P,
      ε ≤ |(regularizedGMC P Xc γ r ω B).toReal -
        ∫ z, f z ∂regularizedGMC P Xc γ r ω| → ENNReal.ofReal ε ≤ gap ω := by
    filter_upwards [hfinite] with ω hfin hω
    let μ  := regularizedGMC P Xc γ r ω
    have hIbMem : MemLp ib 1 μ := by
      have hbd : ∀ᵐ z ∂μ, ‖ib z‖ ≤ 1 := by
        filter_upwards [] with z
        by_cases hz : z ∈ B <;> simp [ib, hz]
      exact @MemLp.of_bound ℂ ℝ _ 1 μ _ hfin ib hib.aestronglyMeasurable 1 hbd
    have hFMem : MemLp f 1 μ := by
      have hbd : ∀ᵐ z ∂μ, ‖f z‖ ≤ 1 := by
        filter_upwards [] with z
        have h := gmcLowerBoxApprox_bounds i n z
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have h0 : 0 ≤ f z := h.1
          linarith
        · exact (h.2)
      exact @MemLp.of_bound ℂ ℝ _ 1 μ _ hfin f
        (gmcLowerBoxApprox i n).continuous.aestronglyMeasurable 1 hbd
    have hIbInt : ∫ z, ib z ∂μ = (μ B).toReal := id (integral_indicator_one hB)
    have hGapEq : ∫⁻ z, edist (ib z) (f z) ∂μ = gap ω := by
      apply lintegral_congr
      intro z
      simp [φ, edist_dist, Real.dist_eq, ib, f]
    have hdist : dist ((μ B).toReal) (∫ z, f z ∂μ) ≤ (gap ω).toReal := by
      rw [← hIbInt, ← hGapEq]
      exact dist_integral_le_lintegral_edist
        (hIbMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1))
        (hFMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1))
    have hdist' : |(μ B).toReal - ∫ z, f z ∂μ| ≤ (gap ω).toReal := hdist
    have hgapTop : gap ω ≠ ∞ := by
      apply ne_of_lt
      calc
        gap ω ≤ ∫⁻ z, (1 : ℝ≥0∞) ∂μ := lintegral_mono hphiBound
        _ = μ Set.univ := by simp
        _ < ∞ := lt_top_iff_ne_top.mpr (@measure_ne_top ℂ _ μ hfin Set.univ)
    have hεgap  := hω.trans hdist'
    exact (ENNReal.ofReal_le_iff_le_toReal hgapTop).2 hεgap
  have hMarkov : P {ω | ENNReal.ofReal ε ≤ gap ω} ≤
      (∫⁻ ω, gap ω ∂P) / ENNReal.ofReal ε := by
    apply meas_ge_le_lintegral_div hgapMeas.aemeasurable
    all_goals simp_all
  calc
    P {ω | ε ≤ |(regularizedGMC P Xc γ r ω B).toReal -
        ∫ z, f z ∂regularizedGMC P Xc γ r ω|} ≤
        P {ω | ENNReal.ofReal ε ≤ gap ω} := measure_mono_ae hEventSub
    _ ≤ (∫⁻ ω, gap ω ∂P) / ENNReal.ofReal ε := hMarkov
    _ = (∫⁻ z, φ z ∂gmcReferenceMeasure) / ENNReal.ofReal ε := by rw [hgapExp]
    _ = _ := by abel

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)

include Ω mΩ P X hX in
/-- Bounded-continuous lower-box ramp integrals of an IsGMCOf limit converge in measure to the
real box mass. -/
theorem testIntegral_boxApprox_tendstoInMeasure

    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (i : ℚ × ℚ) :
    TendstoInMeasure P (fun n ω => ∫ z, gmcLowerBoxApprox i n z ∂M ω) atTop
      (fun ω => (M ω (gmcLowerBox i)).toReal) := by
  let _ := hX.1
  have heval  :=
    measurable_pi_iff.mpr (fun g => (hX.2 g).1)
  have hm0 : equatorGFFRawDistributionSigma X ≤ mΩ := heval.comap_le
  have hFmeas (n : ℕ) : AEMeasurable
      (fun ω => ∫ z, gmcLowerBoxApprox i n z ∂M ω) P := by
    obtain ⟨g, hg, hEq⟩ :=
      equatorGFF_GMC_testIntegral_raw_measurable_version_of_IsGMCOf
        P X hX γ M hM (gmcLowerBoxApprox i n)
    have hg'  := hg.mono hm0 le_rfl
    exact hg'.aemeasurable.congr hEq.symm
  have hGmeas : AEMeasurable (fun ω => (M ω (gmcLowerBox i)).toReal) P := by
    obtain ⟨g, hg, hEq⟩ :=
      equatorGFF_GMC_lowerBox_realMass_raw_version P X hX γ M hM i
    have hg'  := hg.mono hm0 le_rfl
    exact hg'.aemeasurable.congr hEq.symm
  have hpoint : ∀ᵐ ω ∂P, Tendsto
      (fun n => ∫ z, gmcLowerBoxApprox i n z ∂M ω) atTop
      (𝓝 ((M ω (gmcLowerBox i)).toReal)) := by
    apply ae_of_all
    intro ω
    have hfin  := hM.1 ω
    exact @gmcLowerBoxApprox_integral_tendsto i (M ω) hfin
  exact tendstoInMeasure_of_tendsto_ae
    (fun n => (hFmeas n).aestronglyMeasurable) hpoint

include Ω mΩ P X hX in
/-- For any circle-average witness, cutoff mass on a rational lower box converges in measure
to the corresponding mass of an IsGMCOf limit. -/
theorem regularizedGMC_box_mass_tendstoInMeasure

    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (i : ℚ × ℚ) :
    TendstoInMeasure P
      (fun r ω => (regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal) atTop
      (fun ω => (M ω (gmcLowerBox i)).toReal) := by
  let _ := hX.1
  obtain ⟨Yc, hYc, hYlim⟩ := hM.2
  have hConvTest (f : BoundedContinuousFunction ℂ ℝ) :
      TendstoInMeasure P
        (fun r ω => ∫ z, f z ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ z, f z ∂M ω) := by
    have hcut (r : ℝ) :
        (fun ω => ∫ z, f z ∂regularizedGMC P Xc γ r ω) =ᵐ[P]
          fun ω => ∫ z, f z ∂regularizedGMC P Yc γ r ω := by
      filter_upwards [regularizedGMC_ae_eq_of_circleAverage
        P X hX Xc Yc hXc hYc γ r] with ω hω
      rw [hω]
    exact TendstoInMeasure.congr (fun r => (hcut r).symm)
      (Filter.Eventually.of_forall fun _ => rfl) (hYlim f)
  have hBase := testIntegral_boxApprox_tendstoInMeasure P X hX γ M hM i
  have hεevent (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun r => P {ω | ε ≤ |(regularizedGMC P Xc γ r ω
          (gmcLowerBox i)).toReal - (M ω (gmcLowerBox i)).toReal|})
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
    have hlargepos : 0 < large := by
      continuity
    have hsmallpos : 0 < small := by
      continuity
    have hhalf (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
      simp_all
    have hsmallAdd : small + small = large := by
      continuity
    have hlargeAdd : large + large = η := hhalf η
    have hRefEventual  := ENNReal.tendsto_nhds_zero.mp
        (gmcLowerBoxApprox_referenceGap_tendsto i) (small * den) (by positivity)
    have hBaseEventTendsto  :=
      (tendstoInMeasure_iff_norm.mp hBase) ε₃ hε₃
    have hBaseEventual  :=
      ENNReal.tendsto_nhds_zero.mp hBaseEventTendsto small hsmallpos
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hRefEventual.and hBaseEventual)
    let n := N
    have hnRef := (hN N le_rfl).1
    have hnBase := (hN N le_rfl).2
    have hratio  :=
      (ENNReal.div_le_iff hden0 hdenTop).2 hnRef
    have hcutError : ∀ r : ℝ,
        P {ω | ε₃ ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
          ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω‖} ≤ small := by
      intro r
      have hbound := regularizedGMC_lowerBoxApprox_error_le_reference
        P X hX Xc hXc γ r i n ε₃ hε₃
      exact hbound.trans hratio
    have hBaseEvent  := hnBase
    have hmidEventTendsto  :=
      (tendstoInMeasure_iff_norm.mp
        (hConvTest (gmcLowerBoxApprox i n))) ε₃ hε₃
    have hmidEventual  :=
      ENNReal.tendsto_nhds_zero.mp hmidEventTendsto large hlargepos
    have htri (r : ℝ) :
        {ω | ε ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
          (M ω (gmcLowerBox i)).toReal‖} ⊆
        {ω | ε₃ ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
          ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω‖} ∪
        ({ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z
          ∂regularizedGMC P Xc γ r ω) -
          (∫ z, gmcLowerBoxApprox i n z ∂M ω)‖} ∪
         {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂M ω) -
          (M ω (gmcLowerBox i)).toReal‖}) := by
      intro ω hω
      by_contra hnot
      have h₁ : ¬ ε₃ ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
          ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω‖ := by
        intro h
        exact hnot (Or.inl h)
      have h₂ : ¬ ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z
          ∂regularizedGMC P Xc γ r ω) -
          (∫ z, gmcLowerBoxApprox i n z ∂M ω)‖ := by
        grind
      have h₃ : ¬ ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂M ω) -
          (M ω (gmcLowerBox i)).toReal‖ := by
        grind
      have htri₁ := abs_sub_le
        ((regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal)
        (∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω)
        ((M ω (gmcLowerBox i)).toReal)
      have htri₂ := abs_sub_le
        (∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω)
        (∫ z, gmcLowerBoxApprox i n z ∂M ω)
        ((M ω (gmcLowerBox i)).toReal)
      have htri' : ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
          (M ω (gmcLowerBox i)).toReal‖ ≤
          ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
            ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω‖ +
          (‖(∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω) -
            (∫ z, gmcLowerBoxApprox i n z ∂M ω)‖ +
          ‖(∫ z, gmcLowerBoxApprox i n z ∂M ω) -
            (M ω (gmcLowerBox i)).toReal‖) := htri₁.trans (add_le_add_right htri₂ _)
      grind
    filter_upwards [hmidEventual] with r hr
    have hMeasure :
        P {ω | ε ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
          (M ω (gmcLowerBox i)).toReal‖} ≤ small + (large + small) := by
      calc
        _ ≤ P ({ω | ε₃ ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
            ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω‖} ∪
          ({ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z
            ∂regularizedGMC P Xc γ r ω) -
            (∫ z, gmcLowerBoxApprox i n z ∂M ω)‖} ∪
           {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂M ω) -
            (M ω (gmcLowerBox i)).toReal‖})) := measure_mono (htri r)
        _ ≤ P {ω | ε₃ ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
            ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω‖} +
            (P {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z
              ∂regularizedGMC P Xc γ r ω) -
              (∫ z, gmcLowerBoxApprox i n z ∂M ω)‖} +
             P {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂M ω) -
              (M ω (gmcLowerBox i)).toReal‖}) :=
              (measure_union_le _ _).trans
                (add_le_add_right (measure_union_le _ _) _)
        _ ≤ small + (large + small) :=
              add_le_add (hcutError r) (add_le_add hr hBaseEvent)
    calc
      P {ω | ε ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
          (M ω (gmcLowerBox i)).toReal‖}
        ≤ small + (large + small) := hMeasure
      _ = η := by
        calc
          small + (large + small) = (small + small) + large := by ac_rfl
          _ = large + large := by rw [hsmallAdd]
          _ = η := hlargeAdd
      _ ≤ δ := min_le_left δ 1
  rw [tendstoInMeasure_iff_norm]
  simp_all

end
end DOZZ.Proofs
