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




/-- For any circle-average witness, cutoff mass on a rational lower box converges in measure
to the corresponding mass of an IsGMCOf limit. -/
theorem regularizedGMC_box_mass_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (i : ℚ × ℚ) :
    TendstoInMeasure P
      (fun r ω => (regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal) atTop
      (fun ω => (M ω (gmcLowerBox i)).toReal) := by
  have testIntegral_boxApprox_tendstoInMeasure : TendstoInMeasure P (fun n ω => ∫ z, gmcLowerBoxApprox i n z ∂M ω) atTop (fun ω => (M ω (gmcLowerBox i)).toReal) := by
    let _ := hX.1
    have hFmeas n : AEMeasurable
        (fun ω => ∫ z, gmcLowerBoxApprox i n z ∂M ω) P := by
      obtain ⟨g, hg, hEq⟩ :=
        equatorGFF_GMC_testIntegral_raw_measurable_version_of_IsGMCOf
          P X hX γ M hM (gmcLowerBoxApprox i n)
      exact (hg.mono (by dsimp [equatorGFFRawDistributionSigma]; exact (measurable_pi_iff.mpr (fun g => (hX.2 g).1)).comap_le) le_rfl).aemeasurable.congr hEq.symm
    have hpoint : ∀ᵐ ω ∂P, Tendsto
        (fun n => ∫ z, gmcLowerBoxApprox i n z ∂M ω) atTop
        (𝓝 ((M ω (gmcLowerBox i)).toReal)) := by
      apply ae_of_all
      intro ω
      have hfin : IsFiniteMeasure (M ω) := hM.1 ω
      simpa [Measure.real] using @gmcLowerBoxApprox_integral_tendsto i (M ω) hfin
    exact tendstoInMeasure_of_tendsto_ae
      (fun n => (hFmeas n).aestronglyMeasurable) hpoint
  have regularizedGMC_lowerBoxApprox_error_le_reference (r : ℝ) i n (ε : ℝ) (hε : 0 < ε) : P {ω | ε ≤ |(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal - ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω|} ≤ (∫⁻ z, gmcLowerBoxApproxGapIntegrand i n z ∂gmcReferenceMeasure) / ENNReal.ofReal ε := by
    let B := gmcLowerBox i
    let f := gmcLowerBoxApprox i n
    let ib : ℂ → ℝ := B.indicator (fun _ => (1 : ℝ))
    let φ : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal |ib z - f z|
    let gap : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, φ z ∂regularizedGMC P Xc γ r ω
    let _ := hX.1
    have hB : MeasurableSet B := by
      simpa [B] using gmcLowerBox_measurableSet i
    have hib : Measurable ib := measurable_const.indicator hB
    have hφ : Measurable φ := by
      dsimp [φ, ib, f]
      exact ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp
          (hib.sub (gmcLowerBoxApprox i n).continuous.measurable))
    have hphiBound : ∀ z, φ z ≤ 1 := by
      intro z
      have h := gmcLowerBoxApprox_bounds i n z
      have : 0 ≤ f z := by simpa [f, gmcLowerBoxApprox] using h.1
      have : f z ≤ 1 := by simpa [f, gmcLowerBoxApprox] using h.2
      change ENNReal.ofReal |ib z - f z| ≤ 1
      rw [ENNReal.ofReal_le_one, abs_le]
      by_cases hz : z ∈ B
      · simp [ib, hz]
        constructor <;> linarith
      · simp [ib, hz]
        constructor <;> linarith
    have hfinite : ∀ᵐ ω ∂P, IsFiniteMeasure (regularizedGMC P Xc γ r ω) :=
      regularizedGMC_finite_ae P X hX Xc hXc γ r
    have hEventSub : ∀ᵐ ω ∂P,
        ε ≤ |(regularizedGMC P Xc γ r ω B).toReal -
          ∫ z, f z ∂regularizedGMC P Xc γ r ω| → ENNReal.ofReal ε ≤ gap ω := by
      filter_upwards [hfinite] with ω hfin hω
      let μ : Measure ℂ := regularizedGMC P Xc γ r ω
      have hFMem : MemLp f 1 μ := by
        have hbd : ∀ᵐ z ∂μ, ‖f z‖ ≤ 1 := by
          filter_upwards [] with z
          have h := gmcLowerBoxApprox_bounds i n z
          rw [Real.norm_eq_abs, abs_le]
          constructor
          · have h0 : 0 ≤ f z := by simpa [f, gmcLowerBoxApprox] using h.1
            linarith
          · exact (by simpa [f, gmcLowerBoxApprox] using h.2)
        exact @MemLp.of_bound ℂ ℝ _ 1 μ _ hfin f
          (gmcLowerBoxApprox i n).continuous.aestronglyMeasurable 1 hbd
      have hGapEq : ∫⁻ z, edist (ib z) (f z) ∂μ = gap ω := by
        apply lintegral_congr
        intro z
        simp [φ, edist_dist, Real.dist_eq, ib, f]
      have hgapTop : gap ω ≠ ∞ := by
        apply ne_of_lt
        calc
          gap ω ≤ ∫⁻ z, (1 : ℝ≥0∞) ∂μ := by
            apply lintegral_mono
            exact hphiBound
          _ = μ Set.univ := by simp
          _ < ∞ := lt_top_iff_ne_top.mpr (@measure_ne_top ℂ _ μ hfin Set.univ)
      exact (ENNReal.ofReal_le_iff_le_toReal hgapTop).2 (hω.trans (by simpa [Real.dist_eq] using (show dist ((μ B).toReal) (∫ z, f z ∂μ) ≤ (gap ω).toReal by rw [← (show ∫ z, ib z ∂μ = (μ B).toReal by change ∫ z, B.indicator 1 z ∂μ = μ.real B; exact integral_indicator_one hB), ← hGapEq]; exact dist_integral_le_lintegral_edist ((show MemLp ib 1 μ by exact @MemLp.of_bound ℂ ℝ _ 1 μ _ hfin ib hib.aestronglyMeasurable 1 (by filter_upwards [] with z; by_cases hz : z ∈ B <;> simp [ib, hz])).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)) (hFMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)))))
    have hMarkov : P {ω | ENNReal.ofReal ε ≤ gap ω} ≤
        (∫⁻ ω, gap ω ∂P) / ENNReal.ofReal ε := by
      apply meas_ge_le_lintegral_div ((Measure.measurable_lintegral hφ).comp (regularizedGMC_measurable P X hX Xc hXc γ r)).aemeasurable
      · exact (ENNReal.ofReal_pos.mpr hε).ne'
      · exact ENNReal.ofReal_ne_top
    calc
      P {ω | ε ≤ |(regularizedGMC P Xc γ r ω B).toReal -
          ∫ z, f z ∂regularizedGMC P Xc γ r ω|} ≤
          P {ω | ENNReal.ofReal ε ≤ gap ω} := measure_mono_ae hEventSub
      _ ≤ (∫⁻ ω, gap ω ∂P) / ENNReal.ofReal ε := hMarkov
      _ = (∫⁻ z, φ z ∂gmcReferenceMeasure) / ENNReal.ofReal ε := by rw [(show ∫⁻ ω, gap ω ∂P = ∫⁻ z, φ z ∂gmcReferenceMeasure by simpa [gap, φ] using regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r φ hφ)]
      _ = _ := by simp [φ, ib, f, B, gmcLowerBoxApproxGapIntegrand]
  have gmcLowerBoxApprox_referenceGap_tendsto : Tendsto (fun n => ∫⁻ z, gmcLowerBoxApproxGapIntegrand i n z ∂gmcReferenceMeasure) atTop (𝓝 0) := by
    have hbound : ∀ n, ∀ᵐ z ∂gmcReferenceMeasure,
        gmcLowerBoxApproxGapIntegrand i n z ≤ 1 := by
      intro n
      filter_upwards [] with z
      have h := gmcLowerBoxApprox_bounds i n z
      have hpos : 0 ≤ (gmcLowerBoxApprox i n) z := by
        simpa [gmcLowerBoxApprox] using h.1
      have hle : (gmcLowerBoxApprox i n) z ≤ 1 := by
        simpa [gmcLowerBoxApprox] using h.2
      change ENNReal.ofReal
        |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z - (gmcLowerBoxApprox i n) z| ≤ 1
      rw [ENNReal.ofReal_le_one, abs_le]
      by_cases hz : z ∈ gmcLowerBox i
      · simp [Set.indicator, hz]
        exact ⟨by linarith [hle], by linarith [hpos]⟩
      · simp [Set.indicator, hz]
        exact ⟨by linarith [hpos], by linarith [hle]⟩
    have hlim : ∀ᵐ z ∂gmcReferenceMeasure,
        Tendsto (fun n => gmcLowerBoxApproxGapIntegrand i n z) atTop (𝓝 0) := by
      apply ae_of_all
      intro z
      change Tendsto (fun n => ENNReal.ofReal
        |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z -
          gmcLowerBoxApprox i n z|) atTop (𝓝 0)
      let c := (gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z
      convert ((ENNReal.continuous_ofReal.tendsto 0).comp (by simpa using (show Tendsto (fun n => c - (gmcLowerBoxApprox i n) z) atTop (𝓝 0) by simpa [c] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).sub (gmcLowerBoxApprox_tendsto i z))).abs)) using 1
      · funext n
        rfl
      · simp
    simpa using tendsto_lintegral_of_dominated_convergence
      (fun _ : ℂ => (1 : ℝ≥0∞)) (by intro n; apply ENNReal.measurable_ofReal.comp; exact continuous_abs.measurable.comp ((measurable_const.indicator (gmcLowerBox_measurableSet i)).sub (gmcLowerBoxApprox i n).continuous.measurable)) hbound (by simpa using gmcReferenceMeasure_univ_ne_top) hlim
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
  have hBase := testIntegral_boxApprox_tendstoInMeasure
  have hεevent (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun r => P {ω | ε ≤ |(regularizedGMC P Xc γ r ω
          (gmcLowerBox i)).toReal - (M ω (gmcLowerBox i)).toReal|})
        atTop (𝓝 0) := by
    let ε₃ : ℝ := ε / 3
    have hε₃ : 0 < ε₃ := by dsimp [ε₃]; positivity
    let den := ENNReal.ofReal ε₃
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    let η : ℝ≥0∞ := min δ (1 : ℝ≥0∞)
    let large := η / 2
    let small := large / 2
    have hlargepos : 0 < large := by
      dsimp [large]
      exact ENNReal.div_pos (show 0 < η by dsimp [η]; exact lt_min hδ one_pos).ne' (by norm_num)
    have hsmallpos : 0 < small := by
      dsimp [small, large]
      exact ENNReal.div_pos hlargepos.ne' (by norm_num)
    have hhalf (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
      rw [ENNReal.div_add_div_same, ← two_mul, mul_comm]
      exact ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)
    have hRefEventual : ∀ᶠ n : ℕ in atTop,
        (∫⁻ z, gmcLowerBoxApproxGapIntegrand i n z ∂gmcReferenceMeasure) ≤
          small * den := ENNReal.tendsto_nhds_zero.mp
        (gmcLowerBoxApprox_referenceGap_tendsto) (small * den) (by positivity)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hRefEventual.and (ENNReal.tendsto_nhds_zero.mp ((tendstoInMeasure_iff_norm.mp hBase) ε₃ hε₃) small hsmallpos))
    let n := N
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
      have hsmall₁ := lt_of_not_ge (show ¬ ε₃ ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal - ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω‖ by intro h; exact hnot (Or.inl h))
      have hsmall₂ := lt_of_not_ge (show ¬ ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω) - (∫ z, gmcLowerBoxApprox i n z ∂M ω)‖ by intro h; exact hnot (Or.inr (Or.inl h)))
      have hsmall₃ := lt_of_not_ge (show ¬ ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂M ω) - (M ω (gmcLowerBox i)).toReal‖ by intro h; exact hnot (Or.inr (Or.inr h)))
      dsimp [ε₃] at hsmall₁ hsmall₂ hsmall₃
      change ε ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
          (M ω (gmcLowerBox i)).toReal‖ at hω
      exact (not_lt_of_ge hω) (by rw [← (show ε₃ + (ε₃ + ε₃) = ε by dsimp [ε₃]; ring)]; exact lt_of_le_of_lt (show ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal - (M ω (gmcLowerBox i)).toReal‖ ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal - ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω‖ + (‖(∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω) - (∫ z, gmcLowerBoxApprox i n z ∂M ω)‖ + ‖(∫ z, gmcLowerBoxApprox i n z ∂M ω) - (M ω (gmcLowerBox i)).toReal‖) by simpa [Real.norm_eq_abs] using (abs_sub_le ((regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal) (∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω) ((M ω (gmcLowerBox i)).toReal)).trans (add_le_add_right (abs_sub_le (∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω) (∫ z, gmcLowerBoxApprox i n z ∂M ω) ((M ω (gmcLowerBox i)).toReal)) _)) (add_lt_add hsmall₁ (add_lt_add hsmall₂ hsmall₃)))
    filter_upwards [(ENNReal.tendsto_nhds_zero.mp ((tendstoInMeasure_iff_norm.mp (hConvTest (gmcLowerBoxApprox i n))) ε₃ hε₃) large hlargepos)] with r hr
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
              add_le_add ((show ∀ r : ℝ, P {ω | ε₃ ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal - ∫ z, gmcLowerBoxApprox i n z ∂regularizedGMC P Xc γ r ω‖} ≤ small by intro r; simpa [den, Real.norm_eq_abs] using (regularizedGMC_lowerBoxApprox_error_le_reference r i n ε₃ hε₃).trans ((ENNReal.div_le_iff ((ENNReal.ofReal_pos.mpr hε₃).ne') ENNReal.ofReal_ne_top).2 ((hN N le_rfl).1))) r) (add_le_add hr ((hN N le_rfl).2))
    calc
      P {ω | ε ≤ ‖(regularizedGMC P Xc γ r ω (gmcLowerBox i)).toReal -
          (M ω (gmcLowerBox i)).toReal‖}
        ≤ small + (large + small) := hMeasure
      _ = η := by
        calc
          small + (large + small) = (small + small) + large := by ac_rfl
          _ = large + large := by rw [(show small + small = large by dsimp [small, large]; exact hhalf (η / 2))]
          _ = η := (by dsimp [large]; exact hhalf η)
      _ ≤ δ := by dsimp [η]; exact min_le_left δ 1
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simpa [Real.norm_eq_abs] using hεevent ε hε

end
end DOZZ.Proofs
