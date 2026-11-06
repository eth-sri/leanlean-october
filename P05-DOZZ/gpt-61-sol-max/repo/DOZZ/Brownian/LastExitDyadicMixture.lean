/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitKernelRealProjectionLimit

/-!
# Weighted mixture estimates for the dyadic last-exit cells

The deterministic-time cell formula is a mixture of reference kernels, weighted by the probability
of avoiding the barrier after the cell endpoint. This file supplies the elementary bounds used to
pass that mixture to the entrance kernel.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem exists_pos_radius_mem_nhdsWithin_zero
    {S : Set ℝ} (hS : S ∈ 𝓝[>] (0 : ℝ)) :
    ∃ δ > 0, ∀ z, 0 < z → z < δ → z ∈ S := by
  rcases Metric.mem_nhdsWithin_iff.mp hS with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, ?_⟩
  intro z hz hzd
  apply hball
  constructor
  · simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hz] using hzd
  · exact hz

private theorem conditionedH_positive_for_mixture {ν x : ℝ}
    (hν : 0 < ν) (hx : 0 < x) : 0 < conditionedH ν x := by
  rw [conditionedH, ite_eq_right hν.ne']
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  linarith only [mul_pos hν hx]

private theorem conditionedH_mono_for_mixture {ν x y : ℝ}
    (hν : 0 < ν) (hxy : x ≤ y) : conditionedH ν x ≤ conditionedH ν y := by
  simp only [conditionedH, ite_eq_right hν.ne']
  apply sub_le_sub_left
  simp_all

/-- The avoidance weight is a subprobability weight, and it is positive precisely above the
barrier. -/
theorem lastExitAvoidanceFactor_bounds
    {ν c x : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    0 ≤ lastExitAvoidanceFactor ν c x ∧ lastExitAvoidanceFactor ν c x ≤ 1 := by
  by_cases hcx : c < x
  · rw [lastExitAvoidanceFactor, ite_eq_left hcx]
    have hx  := lt_trans hc hcx
    have hxc  := sub_pos.mpr hcx
    have hden := conditionedH_positive_for_mixture hν hx
    have hnum := conditionedH_positive_for_mixture hν hxc
    constructor
    · exact div_nonneg hnum.le hden.le
    · rw [div_le_iff₀ hden]
      simpa using conditionedH_mono_for_mixture hν (sub_le_self x hc.le)
  · simp [lastExitAvoidanceFactor, hcx]

/-- The avoidance weight is measurable as a function of the endpoint state. -/
theorem measurable_lastExitAvoidanceFactor (ν c : ℝ) :
    Measurable (lastExitAvoidanceFactor ν c) := Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (((measurable_conditionedH_ref ν).comp (measurable_id.sub measurable_const)).div
      (measurable_conditionedH_ref ν)) measurable_const

variable (B : Measure BrownianPath) [_inst1 : SFinite B] (hB : IsBrownianReal (fun t p => p t) B) (ν z : ℝ) (hν : 0 < ν) (hz : 0 < z)

include B _inst1 hB ν z hν hz in
/-- A positive-start reference-kernel event has probability between zero and one. -/
theorem brownianUpperConditionedReferenceFutureKernel_real_bounds

    (C : Set (ℚ → ℝ)) :
    0 ≤ (brownianUpperConditionedReferenceFutureKernel B ν hν z).real C ∧
      (brownianUpperConditionedReferenceFutureKernel B ν hν z).real C ≤ 1 := by
  have  :=
    isProbabilityMeasure_brownianBelowConditionedLaw B hB ν z hν hz
  have : IsProbabilityMeasure
      (brownianUpperConditionedReferenceFutureKernel B ν hν z) := by
    rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν z hν hz]
    infer_instance
  simp_all

include B _inst1 hB ν z hν hz in
/-- The positive-start reference kernel is a probability measure. -/
theorem brownianUpperConditionedReferenceFutureKernel_real_univ
     :
    (brownianUpperConditionedReferenceFutureKernel B ν hν z).real Set.univ = 1 := by
  have  :=
    isProbabilityMeasure_brownianBelowConditionedLaw B hB ν z hν hz
  have : IsProbabilityMeasure
      (brownianUpperConditionedReferenceFutureKernel B ν hν z) := by
    rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν z hν hz]
    infer_instance
  simp

/-- The real mass of a measurable event under the reference kernel is measurable in its start. -/
theorem measurable_brownianUpperConditionedReferenceFutureKernel_real
    (B : Measure BrownianPath) [SFinite B]
    (ν : ℝ) (hν : 0 < ν) (C : Set (ℚ → ℝ)) (hC : MeasurableSet C) :
    Measurable (fun z : ℝ =>
      (brownianUpperConditionedReferenceFutureKernel B ν hν z).real C) := ENNReal.measurable_toReal.comp
    (Kernel.measurable_coe (brownianUpperConditionedReferenceFutureKernel B ν hν) hC)

/-- The finite-dimensional laws of the shifted path at the dyadic ceiling converge to the
entrance finite-dimensional law. The proof is a weighted-mixture estimate: near the barrier the
reference kernel is close to its entrance limit, while the total weight of endpoints away from the
barrier is the endpoint tail proved in `LastExitDyadicEndpointTail`. -/
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
        (brownianFirstHitElapsed ncoord
          (fun i => Real.toNNReal (offsets i))))) A).toReal) := by
  classical
  let := hP.2.1
  let project : (ℚ → ℝ) → (Fin ncoord → ℝ) := fun y i => y (offsets i)
  let C  := project ⁻¹' A

  have hproject : Measurable project :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (offsets i))
  have hC  := hA.preimage hproject
  let ts  := fun i => Real.toNNReal (offsets i)
  let ds  := brownianFirstHitElapsed ncoord ts
  have hts0  := fun i => Real.toNNReal_pos.mpr (hoff i)
  have htsmono : StrictMono ts := by
    intro i j hij
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hoff i).le,
      Real.coe_toNNReal _ (hoff j).le]
    exact_mod_cast hmono hij
  have hds  := fun i => brownianFirstHitElapsed_pos ncoord ts hts0 htsmono i
  let M : Measure (Fin ncoord → ℝ) :=
    volume.withDensity (brownianEntranceFinitePDF ν ncoord ds)
  have hMprob : IsProbabilityMeasure M := by
    refine ⟨?_⟩
    change (volume.withDensity (brownianEntranceFinitePDF ν ncoord ds)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa only [setLIntegral_univ] using
      lintegral_brownianEntranceFinitePDF_one Q ν hν hQ ncoord ds hds
  let := hMprob
  let q  := M.real A
  have hq0 : 0 ≤ q := measureReal_nonneg
  have hq1 : q ≤ 1 := by
    aesop
  let cell  := fun m k =>
    dyadicLastExitCellEvent m c Set.univ k
  let hit  := fun m k =>
    conditionedPositiveHistoryHitsOnInterval
      (dyadicLastExitCellStartTime m k) (dyadicLastExitCellEndTime m k) c
  let endpoint  := fun m k p =>
    conditionedPositiveStateAt (dyadicLastExitCellEndTime m k) p
  let weight  := fun m k p =>
    lastExitAvoidanceFactor ν (c : ℝ) (endpoint m k p)
  let kernelProb  := fun z =>
    (brownianUpperConditionedReferenceFutureKernel B ν hν z).real C
  let w  := fun m k => P.real (cell m k)
  let r  := fun m k =>
    ∫ p in hit m k, weight m k p * kernelProb (endpoint m k p - c) ∂P
  have hcellMeas (m k : ℕ) : MeasurableSet (cell m k) := measurableSet_dyadicLastExitCellEvent m c Set.univ MeasurableSet.univ k
  have hcellDisj (m : ℕ) : Pairwise (Disjoint on cell m) := by
    intro k j hne
    exact pairwiseDisjoint_dyadicLastExitCellEvent m c Set.univ hne
  have hcellUnion (m : ℕ) : (⋃ k, cell m k) = Set.univ := by
    dsimp [cell]
    rw [iUnion_dyadicLastExitCellEvent]
    simp [dyadicPositiveLastExitRationalEvent]
  have hfilLe (t : ℝ≥0) :
      conditionedPositiveNaturalFiltration t ≤ ContinuousMap.measurableSpace := by
    refine iSup_le fun s => iSup_le fun _ => ?_
    exact (measurable_conditionedPositiveProcessValue s).comap_le
  have hHitMeas (m k : ℕ) : MeasurableSet (hit m k) := hfilLe (dyadicLastExitCellEndTime m k) _
      (measurableSet_conditionedPositiveHistoryHitsOnInterval _ _ _)
  have hcellMeasureTsum (m : ℕ) :
      (∑' k, P (cell m k)) = P Set.univ := by
    rw [← measure_iUnion (hcellDisj m) (hcellMeas m), hcellUnion]
  have hwSummable (m : ℕ) : Summable (w m) := by
    apply ENNReal.summable_toReal
    rw [hcellMeasureTsum]
    exact measure_ne_top P Set.univ
  have hwTsum (m : ℕ) : ∑' k, w m k = 1 := by
    calc
      ∑' k, w m k = (∑' k, P (cell m k)).toReal :=
        (ENNReal.tsum_toReal_eq (fun k => measure_ne_top P (cell m k))).symm
      _ = (P Set.univ).toReal := by rw [hcellMeasureTsum]
      _ = 1 := by simp
  have hweightIntegral (m k : ℕ) :
      w m k = ∫ p in hit m k, weight m k p ∂P := by
    have hformula := negativeConditionedDyadicLastExitCell_test_measure
      hP hB hν c hc m k Set.univ MeasurableSet.univ
    have hpoint : ∀ p ∈ hit m k,
        weight m k p *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (endpoint m k p - c)).real Set.univ = weight m k p := by
      intro p hp
      by_cases hx : c < endpoint m k p
      · have hz  := sub_pos.mpr hx
        rw [brownianUpperConditionedReferenceFutureKernel_real_univ B hB ν
          (endpoint m k p - c) hν hz]
        simp
      · have hzero : weight m k p = 0 := by
          simp [weight, lastExitAvoidanceFactor, endpoint, le_of_not_gt hx]
        simp [hzero]
    have hH  := hHitMeas m k
    have hraw : P.real (cell m k) =
        ∫ p in hit m k, weight m k p *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (endpoint m k p - c)).real Set.univ ∂P := hformula
    calc
      w m k = P.real (cell m k) := rfl
      _ = ∫ p in hit m k, weight m k p ∂P := by
        rw [hraw]
        exact setIntegral_congr_fun hH (fun p hp => hpoint p hp)
  have hkernelMeas : Measurable kernelProb := measurable_brownianUpperConditionedReferenceFutureKernel_real
      B ν hν C hC
  have hweightMeas (m k : ℕ) : Measurable (weight m k) := (measurable_lastExitAvoidanceFactor ν (c : ℝ)).comp
      (measurable_conditionedPositiveStateAt (dyadicLastExitCellEndTime m k))
  have hkernelAtMeas (m k : ℕ) :
      Measurable (fun p => kernelProb (endpoint m k p - c)) := by
    fun_prop
  have hweightBound (m k : ℕ) (p : BrownianPath) :
      0 ≤ weight m k p ∧ weight m k p ≤ 1 := lastExitAvoidanceFactor_bounds hν hc
  have hrIntegrable (m k : ℕ) :
      Integrable (fun p => weight m k p * kernelProb (endpoint m k p - c)) P := by
    apply Integrable.of_bound ((hweightMeas m k).mul (hkernelAtMeas m k)).aestronglyMeasurable 1
    filter_upwards [] with p
    by_cases hx : c < endpoint m k p
    · have hz  := sub_pos.mpr hx
      have hg := brownianUpperConditionedReferenceFutureKernel_real_bounds
        B hB ν (endpoint m k p - c) hν hz C
      have ha := hweightBound m k p
      change ‖weight m k p * kernelProb (endpoint m k p - c)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha.1 hg.1)]
      exact (mul_le_mul_of_nonneg_right ha.2 hg.1).trans (by simpa using hg.2)
    · have ha : weight m k p = 0 := by
        simp [weight, lastExitAvoidanceFactor, endpoint, le_of_not_gt hx]
      simp [ha]
  have hwIntegrable (m k : ℕ) : Integrable (weight m k) P := by
    apply Integrable.of_bound (hweightMeas m k).aestronglyMeasurable 1
    filter_upwards [] with p
    have ha := hweightBound m k p
    change ‖weight m k p‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg ha.1]
    exact ha.2
  have hrLeW (m k : ℕ) : r m k ≤ w m k := by
    rw [hweightIntegral]
    exact setIntegral_mono_on (hrIntegrable m k).integrableOn
      (hwIntegrable m k).integrableOn
      (hHitMeas m k)
      (fun p _ => by
        by_cases hx : c < endpoint m k p
        · have hz  := sub_pos.mpr hx
          have hg := brownianUpperConditionedReferenceFutureKernel_real_bounds
            B hB ν (endpoint m k p - c) hν hz C
          exact mul_le_of_le_one_right (hweightBound m k p).1 hg.2
        · have ha : weight m k p = 0 := by
            simp [weight, lastExitAvoidanceFactor, endpoint, le_of_not_gt hx]
          simp [ha])
  have hrNonneg (m k : ℕ) : 0 ≤ r m k := by
    have hmeasure := negativeConditionedDyadicLastExitCell_test_measure
      hP hB hν c hc m k C hC
    have hset : negativeConditionedLastExitTimeCell
        (dyadicLastExitCellStartTime m k) (dyadicLastExitCellEndTime m k) c ∩
          dyadicLastExitCellFutureEvent m k c C =
        dyadicLastExitCellEvent m c C k := rfl
    rw [hset] at hmeasure
    change 0 ≤ ∫ p in hit m k,
      weight m k p * kernelProb (endpoint m k p - c) ∂P
    have hmeasure' : P.real (dyadicLastExitCellEvent m c C k) =
        ∫ p in hit m k, weight m k p * kernelProb (endpoint m k p - c) ∂P := hmeasure
    rw [← hmeasure']
    exact measureReal_nonneg
  have hrSummable (m : ℕ) : Summable (r m) := by
    refine Summable.of_nonneg_of_le (hrNonneg m) (hrLeW m) (hwSummable m)
  have hrTsumEq (m : ℕ) :
      (∑' k, r m k) =
        P.real (dyadicPositiveLastExitRationalEvent m (c : ℝ) C) := by
    symm
    exact negativeConditionedDyadicLastExitEvent_measure_eq_tsum
      hP hB hν c hc m C hC
  have hkernelLimit :=
    brownianUpperConditionedReferenceFutureKernel_real_projection_tendsto_entrance
      B hB Q ν hν hQ ncoord offsets hoff hmono A hA
  have htailLimit (δ : ℝ) (hδ : 0 < δ) :
      Tendsto
        (fun m => P.real (dyadicPositiveLastExitRationalEvent m (c : ℝ)
          {y | δ ≤ y 0})) atTop (𝓝 0) := tendsto_measureReal_dyadicPositiveLastExitRationalEvent_zero_eval_ge
      hP hB hν c hc δ hδ
  have happrox (ε : ℝ) (hε : 0 < ε) : ∀ᶠ m : ℕ in atTop,
      q - 2 * ε < P.real (dyadicPositiveLastExitRationalEvent m (c : ℝ) C) ∧
      P.real (dyadicPositiveLastExitRationalEvent m (c : ℝ) C) < q + 2 * ε := by
    have hball : Set.Ioo (q - ε) (q + ε) ∈ 𝓝 q :=
      Ioo_mem_nhds (by linarith) (by linarith)
    have hnearEvent := hkernelLimit.eventually hball
    obtain ⟨δ, hδ, hnear⟩ := exists_pos_radius_mem_nhdsWithin_zero hnearEvent
    let tailWeight  := fun m k p =>
      weight m k p * (if δ ≤ endpoint m k p - c then 1 else 0)
    let tail  := fun m k => ∫ p in hit m k, tailWeight m k p ∂P
    have htailWeightMeas (m k : ℕ) : Measurable (tailWeight m k) := by
      apply (hweightMeas m k).mul
      apply Measurable.ite (measurableSet_le measurable_const
        ((measurable_conditionedPositiveStateAt (dyadicLastExitCellEndTime m k)).sub
          measurable_const))
      · exact measurable_const
      · exact measurable_const
    have htailWeightInt (m k : ℕ) : Integrable (tailWeight m k) P := by
      apply Integrable.of_bound (htailWeightMeas m k).aestronglyMeasurable 1
      filter_upwards [] with p
      have ha := hweightBound m k p
      by_cases hz : δ ≤ endpoint m k p - c <;>
        simp [tailWeight, hz, Real.norm_eq_abs, abs_of_nonneg ha.1, ha.2]
    have htailCellEq (m k : ℕ) :
        tail m k = P.real (dyadicLastExitCellEvent m c {y | δ ≤ y 0} k) := by
      let D : Set (ℚ → ℝ) := {y | δ ≤ y 0}
      have hD : MeasurableSet D := measurableSet_le measurable_const (measurable_pi_apply 0)
      have hformula := negativeConditionedDyadicLastExitCell_test_measure
        hP hB hν c hc m k D hD
      have hpoint : ∀ p ∈ hit m k,
          weight m k p *
            (brownianUpperConditionedReferenceFutureKernel B ν hν
              (endpoint m k p - c)).real D = tailWeight m k p := by
        intro p hp
        by_cases hx : c < endpoint m k p
        · have hz  := sub_pos.mpr hx
          rw [brownianUpperConditionedReferenceFutureKernel_real_initialIci
            B hB ν (endpoint m k p - c) δ hν hz]
        · have hzero : weight m k p = 0 := by
            simp [weight, lastExitAvoidanceFactor, endpoint, le_of_not_gt hx]
          grind
      have hformula' :
          P.real (dyadicLastExitCellEvent m c D k) =
            ∫ p in hit m k, tailWeight m k p ∂P := (hformula.trans (setIntegral_congr_fun (hHitMeas m k) hpoint))
      exact hformula'.symm
    have htailNonneg (m k : ℕ) : 0 ≤ tail m k := by
      rw [htailCellEq]
      exact measureReal_nonneg
    have htailLeW (m k : ℕ) : tail m k ≤ w m k := by
      rw [htailCellEq]
      change P.real (dyadicLastExitCellEvent m c {y | δ ≤ y 0} k) ≤
        P.real (cell m k)
      exact measureReal_mono
        (by
          intro p hp
          exact ⟨hp.1, Set.mem_univ _⟩)
        (measure_ne_top P (cell m k))
    have htailSummable (m : ℕ) : Summable (tail m) :=
      Summable.of_nonneg_of_le (htailNonneg m) (htailLeW m) (hwSummable m)
    have htailTsumEq (m : ℕ) :
        (∑' k, tail m k) =
          P.real (dyadicPositiveLastExitRationalEvent m (c : ℝ)
            {y | δ ≤ y 0}) := by
      have hglobal := negativeConditionedDyadicLastExitEvent_measure_eq_tsum
        hP hB hν c hc m {y | δ ≤ y 0}
          (measurableSet_le measurable_const (measurable_pi_apply 0))
      calc
        (∑' k, tail m k) =
            ∑' k, ∫ p in hit m k,
              weight m k p *
                (brownianUpperConditionedReferenceFutureKernel B ν hν
                  (endpoint m k p - c)).real {y | δ ≤ y 0} ∂P := by
            apply tsum_congr
            intro k
            have hformula := negativeConditionedDyadicLastExitCell_test_measure
              hP hB hν c hc m k {y | δ ≤ y 0}
                (measurableSet_le measurable_const (measurable_pi_apply 0))
            have hformula' :
                P.real (dyadicLastExitCellEvent m c {y | δ ≤ y 0} k) =
                  ∫ p in hit m k,
                    weight m k p *
                      (brownianUpperConditionedReferenceFutureKernel B ν hν
                        (endpoint m k p - c)).real {y | δ ≤ y 0} ∂P := hformula
            exact (htailCellEq m k).trans hformula'
        _ = P.real (dyadicPositiveLastExitRationalEvent m (c : ℝ)
              {y | δ ≤ y 0}) := hglobal.symm
    have htailTendsto : Tendsto (fun m => ∑' k, tail m k) atTop (𝓝 0) := by
      simpa only [htailTsumEq] using htailLimit δ hδ
    have hlocal (m k : ℕ) :
        (q - ε) * w m k - tail m k ≤ r m k := by
      change (q - ε) * w m k - tail m k ≤
        ∫ p in hit m k, weight m k p * kernelProb (endpoint m k p - c) ∂P
      have hpoint : ∀ p ∈ hit m k,
          (q - ε) * weight m k p - tailWeight m k p ≤
            weight m k p * kernelProb (endpoint m k p - c) := by
        intro p hp
        have ha := hweightBound m k p
        by_cases hx : c < endpoint m k p
        · let z := endpoint m k p - c
          have hz : 0 < z := sub_pos.mpr hx
          by_cases hzd : z < δ
          · have hval := hnear z hz hzd
            have hval' : q - ε < kernelProb z ∧ kernelProb z < q + ε := hval


            have hle : 0 ≤ tailWeight m k p := by
              dsimp [tailWeight]
              split_ifs <;> exact mul_nonneg ha.1 (by norm_num)
            have hzero : tailWeight m k p = 0 := by
              simp [tailWeight, z, not_le_of_gt hzd]
            rw [hzero]
            have hgap : 0 ≤ kernelProb z - (q - ε) := by linarith [hval.1]
            have hmul : (q - ε) * weight m k p ≤
                weight m k p * kernelProb z := by
              linarith only [mul_nonneg ha.1 hgap]
            simpa [z, mul_comm] using hmul
          · have hdz  := le_of_not_gt hzd
            have hg := brownianUpperConditionedReferenceFutureKernel_real_bounds
              B hB ν z hν hz C
            have hq  := hq0
            have hqle  := hq1
            have ht : tailWeight m k p = weight m k p := by
              simp [tailWeight, z, hdz]
            rw [ht]
            dsimp [kernelProb]
            linarith only [mul_nonneg ha.1 (by linarith only [hq1, hε] : (0 : ℝ) ≤ 1 + ε - q),
              mul_nonneg ha.1 hg.1]
        · have hzero : weight m k p = 0 := by
            simp [weight, lastExitAvoidanceFactor, endpoint, le_of_not_gt hx]
          have htailzero : tailWeight m k p = 0 := by
            have hnot : ¬ δ ≤ endpoint m k p - c := by
              linarith
            simp [tailWeight, hnot]
          simp [hzero, htailzero]
      have hlin := setIntegral_mono_on
        (((hwIntegrable m k).const_mul (q - ε)).sub (htailWeightInt m k)).integrableOn
        (hrIntegrable m k).integrableOn
        (hHitMeas m k)
        hpoint
      have hrewrite :
          (∫ p in hit m k, (q - ε) * weight m k p - tailWeight m k p ∂P) =
            (q - ε) * w m k - tail m k := by
        rw [integral_sub (((hwIntegrable m k).const_mul (q - ε)).integrableOn)
          (htailWeightInt m k).integrableOn]
        rw [integral_const_mul]
        change (q - ε) * (∫ p in hit m k, weight m k p ∂P) -
          (∫ p in hit m k, tailWeight m k p ∂P) = _
        rw [hweightIntegral]
      simpa [hrewrite, r, tail] using hlin
    have hlocalUpper (m k : ℕ) :
        r m k ≤ (q + ε) * w m k + tail m k := by
      change ∫ p in hit m k,
          weight m k p * kernelProb (endpoint m k p - c) ∂P ≤
        (q + ε) * w m k + tail m k
      have hpoint : ∀ p ∈ hit m k,
          weight m k p * kernelProb (endpoint m k p - c) ≤
            (q + ε) * weight m k p + tailWeight m k p := by
        intro p hp
        have ha := hweightBound m k p
        by_cases hx : c < endpoint m k p
        · let z := endpoint m k p - c
          have hz : 0 < z := sub_pos.mpr hx
          by_cases hzd : z < δ
          · have hval := hnear z hz hzd
            have hval' : q - ε < kernelProb z ∧ kernelProb z < q + ε := hval
            have hlt  := hval'.2
            have hzero : tailWeight m k p = 0 := by
              simp [tailWeight, z, not_le_of_gt hzd]
            rw [hzero]
            have hgap : 0 ≤ (q + ε) - kernelProb z := by linarith [hval.2]
            have hmul : weight m k p * kernelProb z ≤
                (q + ε) * weight m k p := by
              linarith only [mul_nonneg ha.1 hgap]
            simpa [z, mul_comm] using hmul
          · have hdz  := le_of_not_gt hzd
            have hg := brownianUpperConditionedReferenceFutureKernel_real_bounds
              B hB ν z hν hz C
            have ht : tailWeight m k p = weight m k p := by
              simp [tailWeight, z, hdz]
            rw [ht]
            dsimp [kernelProb]
            linarith only [mul_le_of_le_one_right ha.1 hg.2,
              mul_nonneg ha.1 (by linarith only [hq0, hε] : (0 : ℝ) ≤ q + ε)]
        · have hzero : weight m k p = 0 := by
            simp [weight, lastExitAvoidanceFactor, endpoint, le_of_not_gt hx]
          have htailzero : tailWeight m k p = 0 := by
            have hnot : ¬ δ ≤ endpoint m k p - c := by
              intro hbad
              linarith [le_of_not_gt hx, hδ]
            simp [tailWeight, hnot]
          simp [hzero, htailzero]
      have hlin := setIntegral_mono_on (hrIntegrable m k).integrableOn
        (((hwIntegrable m k).const_mul (q + ε)).add
          (htailWeightInt m k)).integrableOn
        (hHitMeas m k)
        hpoint
      have hrewrite :
          (∫ p in hit m k,
            (q + ε) * weight m k p + tailWeight m k p ∂P) =
              (q + ε) * w m k + tail m k := by
        rw [integral_add (((hwIntegrable m k).const_mul (q + ε)).integrableOn)
          (htailWeightInt m k).integrableOn]
        rw [integral_const_mul]
        change (q + ε) * (∫ p in hit m k, weight m k p ∂P) +
          (∫ p in hit m k, tailWeight m k p ∂P) = _
        rw [hweightIntegral]
      simpa [hrewrite, r, tail] using hlin
    have hsumLower (m : ℕ) :
        q - ε - (∑' k, tail m k) ≤ ∑' k, r m k := by
      have hpoint  := hlocal m
      have hscaled  :=
        (hwSummable m).mul_left (q - ε)
      have hleftSummable  :=
        hscaled.sub (htailSummable m)
      have hsum := hleftSummable.tsum_le_tsum hpoint (hrSummable m)
      rw [hscaled.tsum_sub (htailSummable m), (hwSummable m).tsum_mul_left (q - ε),
        hwTsum m] at hsum
      linarith
    have hsumUpper (m : ℕ) :
        (∑' k, r m k) ≤ q + ε + (∑' k, tail m k) := by
      have hpoint  := hlocalUpper m
      have hscaled  :=
        (hwSummable m).mul_left (q + ε)
      have hrightSummable  :=
        hscaled.add (htailSummable m)
      have hsum := (hrSummable m).tsum_le_tsum hpoint hrightSummable
      rw [hscaled.tsum_add (htailSummable m), (hwSummable m).tsum_mul_left (q + ε),
        hwTsum m] at hsum
      linarith
    have heventuallyTail : ∀ᶠ m : ℕ in atTop, (∑' k, tail m k) < ε := by
      have := htailTendsto.eventually (Iio_mem_nhds hε)
      exact this
    filter_upwards [heventuallyTail] with m hm
    rw [← hrTsumEq m]
    constructor <;> linarith only [hsumLower m, hsumUpper m, hm]
  change Tendsto (fun m => P.real (dyadicPositiveLastExitRationalEvent m (c : ℝ) C))
    atTop (𝓝 q)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [happrox (ε / 2) (half_pos hε)] with m hm
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith only [hm.1, hm.2]

end DOZZ.Proofs

end
