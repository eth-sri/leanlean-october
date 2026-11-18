module
public import DOZZ.GMC.Construction.GMCBoxMassLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import DOZZ.GMC.Construction.ReferenceMeasureFinite

open MeasureTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

@[expose] public section

variable {Ω : Type*}

private noncomputable def wbGapInt
    (i : ℚ × ℚ) (n : ℕ) (w : BoundedContinuousFunction ℂ ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (|(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z - gmcLowerBoxApprox i n z| * w z)

private lemma wbGap_abs_le_one (i : ℚ × ℚ) (n : ℕ) (z : ℂ) :
    |(gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z - gmcLowerBoxApprox i n z| ≤ 1 := by
  obtain ⟨h0, h1⟩ := gmcLowerBoxApprox_bounds i n z
  rw [abs_le]
  by_cases hz : z ∈ gmcLowerBox i <;> simp [gmcLowerBoxApprox, hz] <;> exact ⟨by linarith, by linarith⟩


private lemma wbApprox_err_le_ref [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (i : ℚ × ℚ) (n : ℕ) (w : BoundedContinuousFunction ℂ ℝ) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |((regularizedGMC P Xc γ r ω).withDensity
      (fun z => ENNReal.ofReal (w z)) (gmcLowerBox i)).toReal -
      ∫ z, gmcLowerBoxApprox i n z ∂(regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (w z))|} ≤
      (∫⁻ z, wbGapInt i n w z ∂gmcReferenceMeasure) / ENNReal.ofReal ε := by
  let _ := hX.1
  let B := gmcLowerBox i
  let f := gmcLowerBoxApprox i n
  let ib := B.indicator (fun _ : ℂ => (1 : ℝ))
  let W (z : ℂ) := ENNReal.ofReal (w z)
  let φ (z : ℂ) := ENNReal.ofReal |ib z - f z|
  let μ (ω : Ω) := regularizedGMC P Xc γ r ω
  let ν (ω : Ω) := (μ ω).withDensity W
  let gap (ω : Ω) := ∫⁻ z, φ z ∂ν ω
  have hB := gmcLowerBox_measurableSet i
  have hib : Measurable ib := measurable_const.indicator hB
  have hW : Measurable W := ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hφ : Measurable φ := ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hib.sub f.continuous.measurable))
  have hν := Measure.measurable_of_measurable_coe _ fun A hA => by
    have heq : (fun ω => ν ω A) = fun ω => ∫⁻ z, A.indicator W z ∂μ ω :=
      funext fun ω => by dsimp [ν]; rw [withDensity_apply W hA, ← lintegral_indicator hA]
    rw [heq]; exact (Measure.measurable_lintegral (hW.indicator hA)).comp (regularizedGMC_measurable P X hX Xc hXc γ r)
  have hWtot : (∫⁻ ω, ν ω Set.univ ∂P) ≠ ∞ := by
    have heq : (∫⁻ ω, ν ω Set.univ ∂P) = ∫⁻ z, W z ∂gmcReferenceMeasure :=
      (lintegral_congr fun ω => by simp [ν, μ, withDensity_apply]).trans
        (regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r W hW)
    rw [heq]
    refine ne_top_of_le_ne_top (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top gmcReferenceMeasure_univ_ne_top)
      (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Real.norm_eq_abs _ ▸ w.norm_coe_le_norm z)))
  have hfin : ∀ᵐ ω ∂P, IsFiniteMeasure (ν ω) :=
    (ae_lt_top ((Measure.measurable_coe MeasurableSet.univ).comp hν) hWtot).mono fun _ h => ⟨h⟩
  have hsub : ∀ᵐ ω ∂P, ε ≤ |(ν ω B).toReal - ∫ z, f z ∂ν ω| → ENNReal.ofReal ε ≤ gap ω := by
    filter_upwards [hfin] with ω hκ hω
    let _ := hκ
    have hi1 : Integrable ib (ν ω) := Integrable.of_bound hib.aestronglyMeasurable 1
      (ae_of_all _ fun z => by by_cases hz : z ∈ B <;> simp [ib, hz])
    have hf1 : Integrable f (ν ω) := f.integrable (ν ω)
    have hdist : |(ν ω B).toReal - ∫ z, f z ∂ν ω| ≤ (gap ω).toReal := by
      have hd := dist_integral_le_lintegral_edist hi1 hf1
      have hInt : ∫ z, ib z ∂ν ω = (ν ω B).toReal := integral_indicator_one hB
      have hge : (∫⁻ z, edist (ib z) (f z) ∂ν ω) = gap ω :=
        lintegral_congr fun z => by simp [φ, edist_dist, Real.dist_eq]
      rwa [hInt, hge, Real.dist_eq] at hd
    have hgTop : gap ω ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top (ν ω) Set.univ)
      ((lintegral_mono fun z => ENNReal.ofReal_le_one.2 (wbGap_abs_le_one i n z)).trans_eq (by simp))
    exact (ENNReal.ofReal_le_iff_le_toReal hgTop).2 (hω.trans hdist)
  have hExp : ∫⁻ ω, gap ω ∂P = ∫⁻ z, wbGapInt i n w z ∂gmcReferenceMeasure :=
    (lintegral_congr fun ω => lintegral_withDensity_eq_lintegral_mul (μ ω) hW hφ).trans
      ((regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r _ (hW.mul hφ)).trans
        (lintegral_congr fun z => by
          dsimp [W, φ, wbGapInt, ib, f]; rw [ENNReal.ofReal_mul (abs_nonneg _), mul_comm]))
  exact (measure_mono_ae hsub).trans ((meas_ge_le_lintegral_div
    ((Measure.measurable_lintegral hφ).comp hν).aemeasurable
    (ENNReal.ofReal_pos.2 hε).ne' ENNReal.ofReal_ne_top).trans_eq (by dsimp only [Function.comp_apply]; rw [hExp]))

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
  have wbGap_ref_tendsto (_hw : ∀ z, 0 ≤ w z) : Tendsto (fun n => ∫⁻ z, wbGapInt i n w z ∂gmcReferenceMeasure) atTop (𝓝 0) := by
    have hmeas (n : ℕ) : Measurable (wbGapInt i n w) :=
      ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
        ((measurable_const.indicator (gmcLowerBox_measurableSet i)).sub
          (gmcLowerBoxApprox i n).continuous.measurable)).mul w.continuous.measurable)
    have hbd (n : ℕ) : ∀ᵐ z ∂gmcReferenceMeasure, wbGapInt i n w z ≤ ENNReal.ofReal ‖w‖ :=
      ae_of_all _ fun z => by
        have hwz : w z ≤ ‖w‖ := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ w.norm_coe_le_norm z)
        rw [wbGapInt, ENNReal.ofReal_mul (abs_nonneg _)]
        simpa using mul_le_mul (ENNReal.ofReal_le_ofReal (wbGap_abs_le_one i n z))
          (ENNReal.ofReal_le_ofReal hwz) zero_le zero_le
    have hfin : (∫⁻ _ : ℂ, ENNReal.ofReal ‖w‖ ∂gmcReferenceMeasure) ≠ ∞ := by
      rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top gmcReferenceMeasure_univ_ne_top
    have hlim : ∀ᵐ z ∂gmcReferenceMeasure, Tendsto (fun n => wbGapInt i n w z) atTop (𝓝 0) :=
      ae_of_all _ fun z => by
        let b := (gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z
        have hd : Tendsto (fun n => |b - gmcLowerBoxApprox i n z| * w z) atTop (𝓝 0) := by
          simpa [b] using ((tendsto_const_nhds (x := b)).sub (gmcLowerBoxApprox_tendsto i z)).abs.mul_const (w z)
        convert (ENNReal.continuous_ofReal.tendsto 0).comp hd using 1
        · rfl
        · simp
    simpa using tendsto_lintegral_of_dominated_convergence _ hmeas hbd hfin hlim
  let _ := hX.1
  let B := gmcLowerBox i
  let W (z : ℂ) := ENNReal.ofReal (w z)
  let νr (r : ℝ) (ω : Ω) := (regularizedGMC P Xc γ r ω).withDensity W
  let ν (ω : Ω) := (M ω).withDensity W
  have hW : Measurable W := ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hWfin (μ : Measure ℂ) [IsFiniteMeasure μ] : IsFiniteMeasure (μ.withDensity W) :=
    isFiniteMeasure_withDensity (ne_top_of_le_ne_top
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ Set.univ))
      (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Real.norm_eq_abs _ ▸ w.norm_coe_le_norm z))))
  have hIntEq (μ : Measure ℂ) (f : BoundedContinuousFunction ℂ ℝ) :
      ∫ z, f z ∂μ.withDensity W = ∫ z, (w * f) z ∂μ :=
    (integral_withDensity_eq_integral_toReal_smul hW (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) f).trans
      (integral_congr_ae (ae_of_all _ fun z => by simp [W, ENNReal.toReal_ofReal (hw z), smul_eq_mul]))
  have hm0 : equatorGFFRawDistributionSigma X ≤ mΩ :=
    (measurable_pi_iff.mpr fun g => (hX.2 g).1).comap_le
  have hBaseTest : TendstoInMeasure P
      (fun n ω => ∫ z, gmcLowerBoxApprox i n z ∂ν ω) atTop (fun ω => (ν ω B).toReal) := by
    refine tendstoInMeasure_of_tendsto_ae (fun n => ?_) (ae_of_all _ fun ω => ?_)
    · obtain ⟨g, hgm, hgae⟩ := equatorGFF_GMC_testIntegral_raw_measurable_version_of_IsGMCOf
        P X hX γ M hM (w * gmcLowerBoxApprox i n)
      exact ((hgm.mono hm0 le_rfl).aemeasurable.congr
        (hgae.symm.trans (ae_of_all _ fun ω => (hIntEq (M ω) _).symm))).aestronglyMeasurable
    · let _ := hM.1 ω; let _ := hWfin (M ω)
      simpa [Measure.real] using gmcLowerBoxApprox_integral_tendsto (μ := ν ω) i
  obtain ⟨Yc, hYc, hYlim⟩ := hM.2
  have hConvTest (f : BoundedContinuousFunction ℂ ℝ) :
      TendstoInMeasure P (fun r ω => ∫ z, f z ∂νr r ω) atTop (fun ω => ∫ z, f z ∂ν ω) :=
    TendstoInMeasure.congr
      (fun r => (regularizedGMC_ae_eq_of_circleAverage P X hX Xc Yc hXc hYc γ r).mono fun ω hω => by
        show ∫ x, (w * f) x ∂regularizedGMC P Yc γ r ω = ∫ z, f z ∂νr r ω
        dsimp only [νr]; rw [← hIntEq, ← hω])
      (ae_of_all P fun ω => (hIntEq (M ω) f).symm) (hYlim (w * f))
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let ε₃ := ε / 3
  have hε₃ : 0 < ε₃ := by positivity
  let den := ENNReal.ofReal ε₃
  have hden0 : den ≠ 0 := (ENNReal.ofReal_pos.2 hε₃).ne'
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  let η := min δ 1
  have hη := lt_min hδ one_pos
  let q := (η / 2) / 2
  have hq : 0 < q := ENNReal.div_pos (ENNReal.div_pos hη.ne' (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).ne'
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  obtain ⟨n, hnRef, hnBase⟩ := (((wbGap_ref_tendsto hw).eventually_le_const
      (ENNReal.mul_pos hq.ne' hden0)).and
    (((tendstoInMeasure_iff_norm.mp hBaseTest ε₃ hε₃).eventually_le_const hq))).exists
  have hrat : (∫⁻ z, wbGapInt i n w z ∂gmcReferenceMeasure) / den ≤ q :=
    (ENNReal.div_le_iff hden0 ENNReal.ofReal_ne_top).2 hnRef
  filter_upwards [((tendstoInMeasure_iff_norm.mp (hConvTest (gmcLowerBoxApprox i n)) ε₃ hε₃).eventually_le_const
    (ENNReal.div_pos hη.ne' (by norm_num : (2 : ℝ≥0∞) ≠ ∞)))] with r hrMid
  have hsub : {ω | ε ≤ ‖(νr r ω B).toReal - (ν ω B).toReal‖} ⊆
      {ω | ε₃ ≤ ‖(νr r ω B).toReal - ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖} ∪
      ({ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂νr r ω) - ∫ z, gmcLowerBoxApprox i n z ∂ν ω‖} ∪
       {ω | ε₃ ≤ ‖(∫ z, gmcLowerBoxApprox i n z ∂ν ω) - (ν ω B).toReal‖}) := by
    intro ω hω; by_contra! h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs] at h hω
    dsimp [ε₃] at h
    linarith [abs_sub_le (νr r ω B).toReal (∫ z, gmcLowerBoxApprox i n z ∂νr r ω) (ν ω B).toReal,
      abs_sub_le (∫ z, gmcLowerBoxApprox i n z ∂νr r ω) (∫ z, gmcLowerBoxApprox i n z ∂ν ω) (ν ω B).toReal]
  have hcut : P {ω | ε₃ ≤ ‖(νr r ω B).toReal - ∫ z, gmcLowerBoxApprox i n z ∂νr r ω‖} ≤ q := by
    simpa [Real.norm_eq_abs] using (wbApprox_err_le_ref P X hX Xc hXc γ r i n w hε₃).trans hrat
  calc P {ω | ε ≤ ‖(νr r ω B).toReal - (ν ω B).toReal‖}
    _ ≤ q + (η / 2 + q) := ((measure_mono hsub).trans ((measure_union_le _ _).trans
        (add_le_add_right (measure_union_le _ _) _))).trans (add_le_add hcut (add_le_add hrMid hnBase))
    _ = η := by dsimp [q]; rw [← add_assoc, add_right_comm, ENNReal.add_halves, ENNReal.add_halves]
    _ ≤ δ := min_le_left _ _

end
end DOZZ.Proofs
