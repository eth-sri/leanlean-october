/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.AdmissibleCircleTestFatou
public import DOZZ.GMC.Construction.ReferenceMeasureFinite
public import DOZZ.GMC.Construction.FiniteMeasureTotalize
public import DOZZ.GMC.Construction.ReferenceMeasureTight
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.Construction.CircleCutoffTestMass
public import DOZZ.GMC.CircleAverageCutoffIntensity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! An admissible whole-plane circle-chaos version has finite expected total mass. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Distributions CompactlySupported

noncomputable section

namespace DOZZ.Proofs

private def massCutoffCc (n : ℕ) : C_c(ℂ, ℝ) :=
  ⟨⟨fun x => max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)), by fun_prop⟩,
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1))
      fun x hx => by
        rw [Metric.mem_closedBall, dist_zero_right]
        by_contra h
        exact hx (max_eq_left (le_trans (min_le_right _ _) (by linarith)))⟩

private def massCutoff (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  (massCutoffCc n).toBoundedContinuousFunction

section
variable (n : ℕ) (x : ℂ)
include n x

@[simp] private lemma massCutoff_apply :
    massCutoff n x = max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)) := rfl

private lemma massCutoff_nonneg : 0 ≤ massCutoff n x := le_max_left _ _

private lemma massCutoff_le_one : massCutoff n x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)


end

private def cutoffTest (f : BoundedContinuousFunction ℂ ℝ) (R : ℕ) :
    BoundedContinuousFunction ℂ ℝ := f * massCutoff R


private lemma circleIntegral_cutoff_error_le (μ : Measure ℂ) [IsFiniteMeasure μ]
    (f : BoundedContinuousFunction ℂ ℝ) (R : ℕ) :
    ‖∫ x, f x ∂μ - ∫ x, cutoffTest f R x ∂μ‖ ≤
      ‖f‖ * (μ (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ).toReal := by
  let tail := (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ
  have hf := (MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (ae_of_all μ f.norm_coe_le_norm)).integrable le_rfl
  have hg := (MemLp.of_bound (cutoffTest f R).continuous.aestronglyMeasurable ‖cutoffTest f R‖
    (ae_of_all μ (cutoffTest f R).norm_coe_le_norm)).integrable le_rfl
  rw [← integral_sub hf hg]
  refine (norm_integral_le_integral_norm _).trans
    ((integral_mono (hf.sub hg).norm
      ((integrable_const ‖f‖).indicator (s := tail) Metric.isClosed_closedBall.measurableSet.compl)
      fun x => ?_).trans ?_)
  · by_cases hx : x ∈ tail
    · have habs : |1 - massCutoff R x| ≤ 1 :=
        abs_le.2 ⟨by linarith [massCutoff_le_one R x], by linarith [massCutoff_nonneg R x]⟩
      have hle : |f x| * |1 - massCutoff R x| ≤ ‖f‖ :=
        (mul_le_of_le_one_right (abs_nonneg _) habs).trans
          (by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x)
      simpa [cutoffTest, Set.indicator, hx, ← mul_one_sub, abs_mul] using hle
    · have hxr : ‖x‖ ≤ R := by simpa [tail, Metric.mem_closedBall, dist_zero_right] using hx
      have h1 : massCutoff R x = 1 := by simp [min_eq_left (by linarith : 1 ≤ (R : ℝ) + 1 - ‖x‖)]
      simp [cutoffTest, Set.indicator, hx, h1]
  · rw [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet.compl,
      Measure.real_def, smul_eq_mul, mul_comm]

private def tailInnerBcf (R : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max 0 (min 1 (‖x‖ - (R : ℝ)))) (by fun_prop) 1 fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (min_le_left _ _)

@[simp] private lemma tailInnerBcf_apply (R : ℕ) (x : ℂ) :
    tailInnerBcf R x = max 0 (min 1 (‖x‖ - (R : ℝ))) := rfl


/-- An admissible whole-plane circle version, after modification on one null set, satisfies the
global bounded-continuous-test convergence predicate `IsGMCOf`. -/
theorem admissibleCircleVersion_to_IsGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (M : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ M) :
    ∃ N : Ω → Measure ℂ,
      (∀ ω, IsFiniteMeasure (N ω)) ∧ IsGMCOf P X γ N ∧ ∀ᵐ ω ∂P, N ω = M ω := by
  have cutoffTest_hasCompactSupport (f : BoundedContinuousFunction ℂ ℝ) (R : ℕ) : HasCompactSupport (cutoffTest f R : ℂ → ℝ) := 
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 1))
      fun x hx => by
        rw [Metric.mem_closedBall, dist_zero_right]
        by_contra h
        have h0 : massCutoff R x = 0 := by
          simp [max_eq_left (le_trans (min_le_right _ _) (by linarith : (R : ℝ) + 1 - ‖x‖ ≤ 0))]
        exact hx (by simp [cutoffTest, h0])
  have expected_tail_le (R : ℕ) : ∫⁻ ω, M ω (Metric.closedBall (0 : ℂ) ((R : ℝ) + 1))ᶜ ∂P ≤
        gmcReferenceMeasure (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ := by
    have massCutoff_tendsto_one (x : ℂ) : Tendsto (fun n : ℕ => massCutoff n x) atTop (𝓝 1) := by
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
      have h1 : 1 ≤ (n : ℝ) + 1 - ‖x‖ := by
        linarith [hN, (Nat.cast_le (α := ℝ)).2 hn]
      simp [min_eq_left h1]
    let tail := (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ
    let tailLarge := (Metric.closedBall (0 : ℂ) ((R : ℝ) + 1))ᶜ
    let T (n : ℕ) := cutoffTest (tailInnerBcf R) n
    have hT_nn (n : ℕ) (x : ℂ) : 0 ≤ T n x :=
      mul_nonneg (le_max_left _ _) (massCutoff_nonneg n x)
    have hT_mono (x : ℂ) : Monotone fun n => T n x := fun n m hnm =>
      mul_le_mul_of_nonneg_left
        (max_le_max le_rfl (min_le_min le_rfl (by linarith [(Nat.cast_le (α := ℝ)).2 hnm])))
        (le_max_left _ _)
    let A (n : ℕ) (ω : Ω) := ∫⁻ x, ENNReal.ofReal (T n x) ∂M ω
    let B (ω : Ω) := ∫⁻ x, ENNReal.ofReal (tailInnerBcf R x) ∂M ω
    have hAmeas (n : ℕ) : Measurable (A n) :=
      (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp (T n).continuous.measurable)).comp hM.1
    have hABound (n : ℕ) : ∫⁻ ω, A n ω ∂P ≤ gmcReferenceMeasure tail := by
      have hconv (ω : Ω) : A n ω = ENNReal.ofReal (∫ x, T n x ∂M ω) := by
        have hloc : IsFiniteMeasureOnCompacts (M ω) := ⟨fun K hK => hM.2.2.1 ω K hK (subset_univ K)⟩
        have hi := @Continuous.integrable_of_hasCompactSupport ℂ ℝ _ _ _ (M ω) inferInstance
          (T n) hloc (T n).continuous (cutoffTest_hasCompactSupport _ n)
        exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (hT_nn n))).symm
      refine (lintegral_congr_ae (ae_of_all _ hconv)).trans_le
        ((admissibleCircleVersion_expected_test_le P X hX Xc hXc γ M hM (T n) (hT_nn n)
          (cutoffTest_hasCompactSupport _ n)).trans ?_)
      refine (lintegral_mono (g := tail.indicator fun _ => (1 : ℝ≥0∞)) fun x => ?_).trans_eq ?_
      · by_cases hx : x ∈ tail
        · have hle1 : T n x ≤ 1 := (mul_le_of_le_one_right (le_max_left _ _)
            (massCutoff_le_one n x)).trans (max_le zero_le_one (min_le_left _ _))
          simpa [Set.indicator, hx] using ENNReal.ofReal_le_ofReal hle1
        · have hxr : ‖x‖ ≤ R := by simpa [tail, Metric.mem_closedBall, dist_zero_right] using hx
          have h0 : tailInnerBcf R x = 0 := by
            simp [max_eq_left (le_trans (min_le_right _ _) (sub_nonpos.2 hxr))]
          simp [T, cutoffTest, Set.indicator, hx, h0]
      · exact lintegral_indicator_one Metric.isClosed_closedBall.measurableSet.compl
    have houter := lintegral_tendsto_of_tendsto_of_monotone (μ := P) (fun n => (hAmeas n).aemeasurable)
      (ae_of_all P fun ω _ _ hnm => lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hT_mono x hnm))
      (ae_of_all _ fun ω => lintegral_tendsto_of_tendsto_of_monotone
        (fun n => (ENNReal.measurable_ofReal.comp (T n).continuous.measurable).aemeasurable)
        (ae_of_all _ fun x _ _ hnm => ENNReal.ofReal_le_ofReal (hT_mono x hnm))
        (ae_of_all _ fun x => ENNReal.tendsto_ofReal
          (by simpa [T, cutoffTest] using tendsto_const_nhds.mul (massCutoff_tendsto_one x))))
    refine (lintegral_mono fun ω => ?_).trans (le_of_tendsto' houter hABound)
    rw [← lintegral_indicator_one Metric.isClosed_closedBall.measurableSet.compl]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ tailLarge
    · have hxr : (R : ℝ) + 1 < ‖x‖ := lt_of_not_ge
        (by simpa [tailLarge, Metric.mem_closedBall, dist_zero_right] using hx)
      rw [Set.indicator_of_mem hx]
      simp [min_eq_left (by linarith : 1 ≤ ‖x‖ - (R : ℝ))]
    · rw [Set.indicator_of_notMem hx]; simp
  have htail0 : ∫⁻ ω, M ω (Metric.closedBall (0 : ℂ) 1)ᶜ ∂P < ∞ := by
    have hle := expected_tail_le 0
    simp only [Nat.cast_zero, zero_add] at hle
    exact (hle.trans (measure_mono (subset_univ _))).trans_lt
      (lt_top_iff_ne_top.2 gmcReferenceMeasure_univ_ne_top)
  have hfin_ae : ∀ᵐ ω ∂P, IsFiniteMeasure (M ω) := by
    filter_upwards [ae_lt_top ((Measure.measurable_coe
      Metric.isClosed_closedBall.measurableSet.compl).comp hM.1) htail0.ne] with ω hω
    refine ⟨?_⟩
    rw [← Set.union_compl_self (Metric.closedBall (0 : ℂ) 1)]
    exact (measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨hM.2.2.1 ω _ (isCompact_closedBall 0 1) (subset_univ _), hω⟩)
  obtain ⟨N, hNmeas, hNfinite, hNM⟩ := exists_everywhere_finite_measure_version P M hM.1 hfin_ae
  refine ⟨N, hNfinite, ⟨hNfinite, ⟨Xc, hXc, fun f => tendstoInMeasure_iff_norm.2 fun ε hε => ?_⟩⟩, hNM⟩
  let q := ENNReal.ofReal (ε / (3 * (‖f‖ + 1)))
  have hq0 : q ≠ 0 := (ENNReal.ofReal_pos.2 (div_pos hε (by positivity))).ne'
  let tail (n : ℕ) := (Metric.closedBall (0 : ℂ) ((n + 1 : ℕ) : ℝ))ᶜ
  let refTail (n : ℕ) := (Metric.closedBall (0 : ℂ) (n : ℝ))ᶜ
  have htail_err {μ : Ω → Measure ℂ} (hμm : Measurable μ) (hμf : ∀ᵐ ω ∂P, IsFiniteMeasure (μ ω))
      (n : ℕ) (hμt : ∫⁻ ω, μ ω (tail n) ∂P ≤ gmcReferenceMeasure (refTail n)) :
      P {ω | ε / 3 ≤ ‖(∫ x, f x ∂μ ω) - (∫ x, cutoffTest f (n + 1) x ∂μ ω)‖} ≤
        gmcReferenceMeasure (refTail n) / q := by
    have hIncl : ∀ᵐ ω ∂P, ω ∈ {ω | ε / 3 ≤ ‖(∫ x, f x ∂μ ω) - (∫ x, cutoffTest f (n + 1) x ∂μ ω)‖} →
        ω ∈ {ω | q ≤ μ ω (tail n)} := by
      filter_upwards [hμf] with ω hfin hω
      have herr := @circleIntegral_cutoff_error_le (μ ω) hfin f (n + 1)
      have hlarge : ε / 3 ≤ ‖f‖ * (μ ω (tail n)).toReal := hω.trans herr
      refine (ENNReal.ofReal_le_iff_le_toReal (@measure_ne_top _ _ (μ ω) hfin _)).2 ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [ENNReal.toReal_nonneg (a := μ ω (tail n))]
    exact (measure_mono_ae hIncl).trans
      ((meas_ge_le_lintegral_div ((Measure.measurable_coe
        Metric.isClosed_closedBall.measurableSet.compl).comp hμm).aemeasurable
        hq0 ENNReal.ofReal_ne_top).trans (ENNReal.div_le_div_right hμt q))
  have hsub_tail (n : ℕ) : tail n ⊆ refTail n := fun x hx => by
    have hlt : (n : ℝ) + 1 < ‖x‖ := not_le.1
      (by simpa [tail, Metric.mem_closedBall, dist_zero_right, Nat.cast_add, Nat.cast_one] using hx)
    simp only [refTail, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
    linarith
  have herr_reg (n : ℕ) (r : ℝ) := htail_err (regularizedGMC_measurable P X hX Xc hXc γ r)
    (regularizedGMC_finite_ae P X hX Xc hXc γ r) n
    ((regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ r (tail n)
      Metric.isClosed_closedBall.measurableSet.compl).trans_le (measure_mono (hsub_tail n)))
  have herr_N (n : ℕ) : P {ω | ε / 3 ≤ ‖(∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖} ≤
      gmcReferenceMeasure (refTail n) / q := by
    simpa only [norm_sub_rev] using htail_err hNmeas (ae_of_all _ hNfinite) n (by
      refine (lintegral_congr_ae (g := fun ω => M ω (tail n)) (hNM.mono fun ω hω => ?_)).trans_le ?_
      · simp [hω]
      · simpa [tail, refTail, Nat.cast_add, Nat.cast_one] using
          expected_tail_le n)
  have hcore (n : ℕ) : Tendsto (fun r : ℝ => P {ω | ε / 3 ≤
      ‖(∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
        (∫ x, cutoffTest f (n + 1) x ∂N ω)‖}) atTop (𝓝 0) := by
    let fc := cutoffTest f (n + 1)
    have hM_tm := TendstoInMeasure.congr
      (fun r => Eventually.of_forall fun ω => circleCutoff_testMass_eq_regularizedGMC P X hX Xc hXc γ r ω fc)
      (Eventually.of_forall fun _ => rfl)
      (hM.2.2.2 fc (cutoffTest_hasCompactSupport f (n + 1)) (subset_univ _))
    simpa [fc, norm_sub_rev] using tendstoInMeasure_iff_norm.1
      (tendstoInMeasure_integral_after_ae_measure_change _ M N fc hNM hM_tm)
      (ε / 3) (by positivity)
  have hTailDiv : Tendsto (fun n : ℕ => gmcReferenceMeasure (refTail n) / q + 0 +
      gmcReferenceMeasure (refTail n) / q) atTop (𝓝 0) := by
    have hd : Tendsto (fun n : ℕ => gmcReferenceMeasure (refTail n) / q) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.div_const (b := q)
        gmcReferenceMeasure_compl_closedBall_tendsto_zero (Or.inr hq0)
    have h0 : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
    simpa using (hd.add h0).add hd
  refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
  obtain ⟨n, hn⟩ := eventually_atTop.1 (hTailDiv.eventually (Iio_mem_nhds hδ))
  filter_upwards [((tendsto_const_nhds.add (hcore n)).add tendsto_const_nhds).eventually
    (Iio_mem_nhds (hn n le_rfl))] with r hr
  refine le_of_lt (lt_of_le_of_lt ?_ hr)
  let a (ω : Ω) := ∫ x, f x ∂regularizedGMC P Xc γ r ω
  let b (ω : Ω) := ∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω
  let c (ω : Ω) := ∫ x, cutoffTest f (n + 1) x ∂N ω
  let d (ω : Ω) := ∫ x, f x ∂N ω
  have hsub : {ω | ε ≤ ‖a ω - d ω‖} ⊆
      {ω | ε / 3 ≤ ‖a ω - b ω‖} ∪ ({ω | ε / 3 ≤ ‖b ω - c ω‖} ∪ {ω | ε / 3 ≤ ‖c ω - d ω‖}) := by
    intro ω hω; by_contra hnot
    simp only [mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot hω
    have htri : ‖a ω - d ω‖ ≤ ‖a ω - b ω‖ + ‖b ω - c ω‖ + ‖c ω - d ω‖ :=
      (norm_sub_le_norm_sub_add_norm_sub (a ω) (c ω) (d ω)).trans
        (add_le_add (norm_sub_le_norm_sub_add_norm_sub (a ω) (b ω) (c ω)) le_rfl)
    linarith
  calc P {ω | ε ≤ ‖a ω - d ω‖}
    _ ≤ P ({ω | ε / 3 ≤ ‖a ω - b ω‖} ∪ ({ω | ε / 3 ≤ ‖b ω - c ω‖} ∪ {ω | ε / 3 ≤ ‖c ω - d ω‖})) :=
      measure_mono hsub
    _ ≤ P {ω | ε / 3 ≤ ‖a ω - b ω‖} + (P {ω | ε / 3 ≤ ‖b ω - c ω‖} + P {ω | ε / 3 ≤ ‖c ω - d ω‖}) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ gmcReferenceMeasure (refTail n) / q + P {ω | ε / 3 ≤ ‖b ω - c ω‖} +
        gmcReferenceMeasure (refTail n) / q := by
      rw [← add_assoc]
      exact add_le_add (add_le_add (herr_reg n r) le_rfl) (herr_N n)

end DOZZ.Proofs
