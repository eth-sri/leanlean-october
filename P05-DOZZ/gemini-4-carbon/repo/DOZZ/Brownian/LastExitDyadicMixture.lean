/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitKernelRealProjectionLimit

/-!
# Weighted mixture estimates for the dyadic last-exit cells
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The avoidance weight is a subprobability weight, and it is positive precisely above the
barrier. -/
theorem lastExitAvoidanceFactor_bounds
    {ν c x : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    0 ≤ lastExitAvoidanceFactor ν c x ∧ lastExitAvoidanceFactor ν c x ≤ 1 := by
  have hpos {y : ℝ} (hy : 0 < y) : 0 < conditionedH ν y := by
    rw [conditionedH, ite_eq_right hν.ne']
    exact sub_pos.2 (Real.exp_lt_one_iff.2 (by nlinarith))
  by_cases hcx : c < x
  · rw [lastExitAvoidanceFactor, ite_eq_left hcx]
    have hden := hpos (hc.trans hcx)
    refine ⟨div_nonneg (hpos (sub_pos.2 hcx)).le hden.le, (div_le_iff₀ hden).2 ?_⟩
    simp only [one_mul, conditionedH, ite_eq_right hν.ne']
    exact sub_le_sub_left (Real.exp_le_exp.2 (by nlinarith)) _
  · simp [lastExitAvoidanceFactor, hcx]

/-- The avoidance weight is measurable as a function of the endpoint state. -/
theorem measurable_lastExitAvoidanceFactor (ν c : ℝ) :
    Measurable (lastExitAvoidanceFactor ν c) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (((measurable_conditionedH_ref ν).comp (measurable_id.sub measurable_const)).div
      (measurable_conditionedH_ref ν)) measurable_const

/-- The finite-dimensional laws of the shifted path at the dyadic ceiling converge to the
entrance finite-dimensional law. -/
theorem negativeConditionedDyadicLastExit_finiteProjection_tendsto_entrance
    {ν : ℝ} {P B Q : Measure BrownianPath} [IsFiniteMeasure P] [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (ncoord : ℕ) (offsets : Fin ncoord → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets)
    (A : Set (Fin ncoord → ℝ)) (hA : MeasurableSet A) :
    Tendsto
      (fun n => P.real (dyadicPositiveLastExitRationalEvent n (c : ℝ)
        {y | (fun i => y (offsets i)) ∈ A}))
      atTop
      (𝓝 ((volume.withDensity (brownianEntranceFinitePDF ν ncoord
        (brownianFirstHitElapsed ncoord (fun i => Real.toNNReal (offsets i))))) A).toReal) := by
  let _ := hP.2.1
  let C : Set (ℚ → ℝ) := {y | (fun i => y (offsets i)) ∈ A}
  have hC : MeasurableSet C := hA.preimage (measurable_pi_iff.2 fun i => measurable_pi_apply (offsets i))
  let ts : Fin ncoord → ℝ≥0 := fun i => Real.toNNReal (offsets i)
  let ds := brownianFirstHitElapsed ncoord ts
  have hts_mono : StrictMono ts := fun i j hij => by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hoff i).le, Real.coe_toNNReal _ (hoff j).le]
    exact_mod_cast hmono hij
  have hds : ∀ i, 0 < ds i := brownianFirstHitElapsed_pos ncoord ts
    (fun i => Real.toNNReal_pos.2 (hoff i)) hts_mono
  let M := volume.withDensity (brownianEntranceFinitePDF ν ncoord ds)
  have hMprob : IsProbabilityMeasure M := ⟨by
    rw [show M = volume.withDensity (brownianEntranceFinitePDF ν ncoord ds) from rfl,
      withDensity_apply _ MeasurableSet.univ]
    simpa only [setLIntegral_univ] using lintegral_brownianEntranceFinitePDF_one Q ν hν hQ ncoord ds hds⟩
  let q := M.real A
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := (measureReal_mono (subset_univ A)).trans_eq (by simp [M])
  have hker_prob (z : ℝ) (hz : 0 < z) :
      IsProbabilityMeasure (brownianUpperConditionedReferenceFutureKernel B ν hν z) := by
    have := isProbabilityMeasure_brownianBelowConditionedLaw B hB ν z hν hz
    rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν z hν hz]
    infer_instance
  let hit (m k : ℕ) := conditionedPositiveHistoryHitsOnInterval
    (dyadicLastExitCellStartTime m k) (dyadicLastExitCellEndTime m k) c
  let endpt (m k : ℕ) (p : BrownianPath) := conditionedPositiveStateAt (dyadicLastExitCellEndTime m k) p
  let wt (m k : ℕ) (p : BrownianPath) := lastExitAvoidanceFactor ν (c : ℝ) (endpt m k p)
  let kProb (E : Set (ℚ → ℝ)) (z : ℝ) := (brownianUpperConditionedReferenceFutureKernel B ν hν z).real E
  have hHitMeas (m k : ℕ) : MeasurableSet (hit m k) :=
    (iSup_le fun s => iSup_le fun _ => (measurable_conditionedPositiveProcessValue s).comap_le :
      conditionedPositiveNaturalFiltration (dyadicLastExitCellEndTime m k) ≤ ContinuousMap.measurableSpace) _
      (measurableSet_conditionedPositiveHistoryHitsOnInterval _ _ _)
  have hwt_m (m k : ℕ) : Measurable (wt m k) :=
    (measurable_lastExitAvoidanceFactor ν (c : ℝ)).comp (measurable_conditionedPositiveStateAt _)
  have hwt_b (m k : ℕ) (p : BrownianPath) : 0 ≤ wt m k p ∧ wt m k p ≤ 1 := lastExitAvoidanceFactor_bounds hν hc
  have hwt_int (m k : ℕ) : Integrable (wt m k) P :=
    Integrable.of_bound (hwt_m m k).aestronglyMeasurable 1 (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hwt_b m k p).1]; exact (hwt_b m k p).2)
  have hkp_int (m k : ℕ) {E : Set (ℚ → ℝ)} (hE : MeasurableSet E) :
      Integrable (fun p => wt m k p * kProb E (endpt m k p - c)) P := by
    have hm : Measurable fun z : ℝ => kProb E z :=
      ENNReal.measurable_toReal.comp (Kernel.measurable_coe _ hE)
    have hjm : Measurable fun p => wt m k p * kProb E (endpt m k p - c) :=
      (hwt_m m k).mul (hm.comp ((measurable_conditionedPositiveStateAt _).sub measurable_const))
    refine Integrable.of_bound hjm.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
    by_cases hx : (c : ℝ) < endpt m k p
    · let _ := hker_prob _ (sub_pos.2 hx)
      have hb : kProb E (endpt m k p - c) ≤ 1 := (measureReal_mono (subset_univ E)).trans_eq (by simp [kProb])
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hwt_b m k p).1 measureReal_nonneg)]
      exact (mul_le_of_le_one_left measureReal_nonneg (hwt_b m k p).2).trans hb
    · have h0 : wt m k p = 0 := by simp [wt, lastExitAvoidanceFactor, endpt, hx]
      simp [h0]
  let w (m k : ℕ) := P.real (dyadicLastExitCellEvent m c Set.univ k)
  let r (m k : ℕ) := P.real (dyadicLastExitCellEvent m c C k)
  have hw_eq (m k : ℕ) : w m k = ∫ p in hit m k, wt m k p ∂P := by
    have hf := negativeConditionedDyadicLastExitCell_test_measure hP hB hν c hc m k Set.univ MeasurableSet.univ
    refine (by simpa [w, hit, endpt, wt, dyadicLastExitCellEvent, dyadicLastExitCellFutureEvent] using hf :
      w m k = ∫ p in hit m k, wt m k p * kProb Set.univ (endpt m k p - c) ∂P).trans
      (setIntegral_congr_fun (hHitMeas m k) fun p _ => ?_)
    by_cases hx : (c : ℝ) < endpt m k p
    · let _ := hker_prob _ (sub_pos.2 hx); simp [kProb]
    · have h0 : wt m k p = 0 := by simp [wt, lastExitAvoidanceFactor, endpt, hx]
      simp [h0]
  have hcell_sum (m : ℕ) : (∑' k, P (dyadicLastExitCellEvent m c Set.univ k)) = P Set.univ := by
    rw [← measure_iUnion (fun k j hne => pairwiseDisjoint_dyadicLastExitCellEvent m c Set.univ hne)
      (fun k => measurableSet_dyadicLastExitCellEvent m c Set.univ MeasurableSet.univ k),
      iUnion_dyadicLastExitCellEvent]
    simp [dyadicPositiveLastExitRationalEvent]
  have hw_sum (m : ℕ) : Summable (w m) :=
    ENNReal.summable_toReal (by rw [hcell_sum]; exact measure_ne_top P Set.univ)
  have hw_tsum (m : ℕ) : ∑' k, w m k = 1 := by
    rw [show (∑' k, w m k) = (∑' k, P (dyadicLastExitCellEvent m c Set.univ k)).toReal from
      (ENNReal.tsum_toReal_eq fun _ => measure_ne_top _ _).symm, hcell_sum]; simp
  have hsub_cell (m k : ℕ) (E : Set (ℚ → ℝ)) :
      dyadicLastExitCellEvent m c E k ⊆ dyadicLastExitCellEvent m c Set.univ k :=
    fun _ hp => ⟨hp.1, mem_univ _⟩
  have hr_sum (m : ℕ) : Summable (r m) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg)
      (fun k => measureReal_mono (hsub_cell m k C)) (hw_sum m)
  have hr_tsum (m : ℕ) : (∑' k, r m k) = P.real (dyadicPositiveLastExitRationalEvent m c C) := by
    rw [negativeConditionedDyadicLastExitEvent_measure_eq_tsum hP hB hν c hc m C hC]
    refine tsum_congr fun k => ?_
    simpa [r, hit, endpt, wt, kProb, dyadicLastExitCellEvent, dyadicLastExitCellFutureEvent] using
      negativeConditionedDyadicLastExitCell_test_measure hP hB hν c hc m k C hC
  have hker_lim := brownianUpperConditionedReferenceFutureKernel_real_projection_tendsto_entrance
    B hB Q ν hν hQ ncoord offsets hoff hmono A hA
  change Tendsto (fun n => P.real (dyadicPositiveLastExitRationalEvent n (c : ℝ) C)) atTop (𝓝 q)
  rw [Metric.tendsto_nhds]
  intro ε₀ hε₀
  let ε := ε₀ / 3
  have hε : 0 < ε := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1
    (hker_lim.eventually (Ioo_mem_nhds (by linarith : q - ε < q) (by linarith : q < q + ε)))
  let D : Set (ℚ → ℝ) := {y | δ / 2 ≤ y 0}
  have hD : MeasurableSet D := measurableSet_le measurable_const (measurable_pi_apply 0)
  let tail (m k : ℕ) := P.real (dyadicLastExitCellEvent m c D k)
  have htail_sum (m : ℕ) : Summable (tail m) :=
    Summable.of_nonneg_of_le (fun _ => measureReal_nonneg)
      (fun k => measureReal_mono (hsub_cell m k D)) (hw_sum m)
  have htail_tsum (m : ℕ) : (∑' k, tail m k) = P.real (dyadicPositiveLastExitRationalEvent m c D) := by
    rw [negativeConditionedDyadicLastExitEvent_measure_eq_tsum hP hB hν c hc m D hD]
    refine tsum_congr fun k => ?_
    simpa [tail, hit, endpt, wt, kProb, dyadicLastExitCellEvent, dyadicLastExitCellFutureEvent] using
      negativeConditionedDyadicLastExitCell_test_measure hP hB hν c hc m k D hD
  have htail_ev : ∀ᶠ m in atTop, (∑' k, tail m k) < ε := by
    simpa only [htail_tsum] using
      (tendsto_measureReal_dyadicPositiveLastExitRationalEvent_zero_eval_ge hP hB hν c hc (δ / 2)
        (half_pos hδ)).eventually (Iio_mem_nhds hε)
  filter_upwards [htail_ev] with m hm
  have hcell_bd (k : ℕ) : (q - ε) * w m k - tail m k ≤ r m k ∧ r m k ≤ (q + ε) * w m k + tail m k := by
    have hr_k : r m k = ∫ p in hit m k, wt m k p * kProb C (endpt m k p - c) ∂P := by
      simpa [r, hit, endpt, wt, kProb, dyadicLastExitCellEvent, dyadicLastExitCellFutureEvent] using
        negativeConditionedDyadicLastExitCell_test_measure hP hB hν c hc m k C hC
    have ht_k : tail m k = ∫ p in hit m k, wt m k p * kProb D (endpt m k p - c) ∂P := by
      simpa [tail, hit, endpt, wt, kProb, dyadicLastExitCellEvent, dyadicLastExitCellFutureEvent] using
        negativeConditionedDyadicLastExitCell_test_measure hP hB hν c hc m k D hD
    rw [hr_k, ht_k, hw_eq, ← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((hwt_int m k).const_mul _).integrableOn (hkp_int m k hD).integrableOn,
      ← integral_add ((hwt_int m k).const_mul _).integrableOn (hkp_int m k hD).integrableOn]
    refine ⟨setIntegral_mono_on (((hwt_int m k).const_mul _).sub (hkp_int m k hD)).integrableOn
      (hkp_int m k hC).integrableOn (hHitMeas m k) fun p _ => ?_,
      setIntegral_mono_on (hkp_int m k hC).integrableOn
        (((hwt_int m k).const_mul _).add (hkp_int m k hD)).integrableOn (hHitMeas m k) fun p _ => ?_⟩
    · by_cases hx : (c : ℝ) < endpt m k p
      · let z := endpt m k p - c
        have hz : 0 < z := sub_pos.2 hx
        let _ := hker_prob z hz
        have hDval : kProb D z = if δ / 2 ≤ z then 1 else 0 :=
          brownianUpperConditionedReferenceFutureKernel_real_initialIci B hB ν z (δ / 2) hν hz
        change (q - ε) * wt m k p - wt m k p * kProb D z ≤ wt m k p * kProb C z
        rw [hDval]
        by_cases hzd : z < δ / 2
        · rw [ite_eq_right (not_le_of_gt hzd), mul_zero, sub_zero]
          have hnear : q - ε < kProb C z ∧ kProb C z < q + ε :=
            hball ⟨by simp [Metric.mem_ball, Real.dist_eq, abs_of_pos hz]; linarith, hz⟩
          nlinarith [(hwt_b m k p).1, hnear.1]
        · rw [ite_eq_left (le_of_not_gt hzd), mul_one]
          have hc0 : 0 ≤ kProb C z := measureReal_nonneg
          nlinarith [(hwt_b m k p).1, hq1, hc0]
      · have h0 : wt m k p = 0 := by simp [wt, lastExitAvoidanceFactor, endpt, hx]
        simp [h0]
    · by_cases hx : (c : ℝ) < endpt m k p
      · let z := endpt m k p - c
        have hz : 0 < z := sub_pos.2 hx
        let _ := hker_prob z hz
        have hDval : kProb D z = if δ / 2 ≤ z then 1 else 0 :=
          brownianUpperConditionedReferenceFutureKernel_real_initialIci B hB ν z (δ / 2) hν hz
        change wt m k p * kProb C z ≤ (q + ε) * wt m k p + wt m k p * kProb D z
        rw [hDval]
        by_cases hzd : z < δ / 2
        · rw [ite_eq_right (not_le_of_gt hzd), mul_zero, add_zero]
          have hnear : q - ε < kProb C z ∧ kProb C z < q + ε :=
            hball ⟨by simp [Metric.mem_ball, Real.dist_eq, abs_of_pos hz]; linarith, hz⟩
          nlinarith [(hwt_b m k p).1, hnear.2]
        · rw [ite_eq_left (le_of_not_gt hzd), mul_one]
          have hc1 : kProb C z ≤ 1 := (measureReal_mono (subset_univ C)).trans_eq (by simp [kProb])
          nlinarith [(hwt_b m k p).1, hq0, hc1]
      · have h0 : wt m k p = 0 := by simp [wt, lastExitAvoidanceFactor, endpt, hx]
        simp [h0]
  have hlo : q - ε - ∑' k, tail m k ≤ ∑' k, r m k := by
    have hs := ((hw_sum m).mul_left (q - ε)).sub (htail_sum m)
    have h := hs.tsum_le_tsum (fun k => (hcell_bd k).1) (hr_sum m)
    rwa [((hw_sum m).mul_left (q - ε)).tsum_sub (htail_sum m), (hw_sum m).tsum_mul_left, hw_tsum m, mul_one] at h
  have hhi : ∑' k, r m k ≤ q + ε + ∑' k, tail m k := by
    have hs := ((hw_sum m).mul_left (q + ε)).add (htail_sum m)
    have h := (hr_sum m).tsum_le_tsum (fun k => (hcell_bd k).2) hs
    rwa [((hw_sum m).mul_left (q + ε)).tsum_add (htail_sum m), (hw_sum m).tsum_mul_left, hw_tsum m, mul_one] at h
  rw [Real.dist_eq, ← hr_tsum m, abs_lt]
  dsimp [ε] at hm hlo hhi
  constructor <;> linarith

end DOZZ.Proofs

end
