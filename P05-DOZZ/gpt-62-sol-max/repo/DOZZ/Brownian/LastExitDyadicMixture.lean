/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitKernelRealProjectionLimit
public import DOZZ.Brownian.ConditionedKernelAlgebra

/-!
# Weighted mixture estimates for the dyadic last-exit cells

The deterministic-time cell formula is a mixture of reference kernels, weighted by the probability
of avoiding the barrier after the cell endpoint. This file supplies the elementary bounds used to
pass that mixture to the entrance kernel.
-/

@[expose] public section

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

private theorem conditionedH_mono_for_mixture {ν x y : ℝ}
    (hν : 0 < ν) (hxy : x ≤ y) : conditionedH ν x ≤ conditionedH ν y := by
  simp only [conditionedH, ite_eq_right hν.ne']
  apply sub_le_sub_left
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hxy (by linarith only [hν])

/-- The avoidance weight is a subprobability weight, and it is positive precisely above the
barrier. -/
theorem lastExitAvoidanceFactor_bounds
    {ν c x : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    0 ≤ lastExitAvoidanceFactor ν c x ∧ lastExitAvoidanceFactor ν c x ≤ 1 := by
  by_cases hcx : c < x
  · rw [lastExitAvoidanceFactor, ite_eq_left hcx]
    have hx  := lt_trans hc hcx
    have hxc  := sub_pos.mpr hcx
    have hden := conditionedH_pos hν.le hx
    have hnum := conditionedH_pos hν.le hxc
    constructor
    · exact div_nonneg hnum.le hden.le
    · rw [div_le_iff₀ hden]
      simpa using conditionedH_mono_for_mixture hν (sub_le_self x hc.le)
  · simp [lastExitAvoidanceFactor, hcx]

/-- The avoidance weight is measurable as a function of the endpoint state. -/
theorem measurable_lastExitAvoidanceFactor (ν c : ℝ) :
    Measurable (lastExitAvoidanceFactor ν c) := by
  unfold lastExitAvoidanceFactor
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (((measurable_conditionedH_ref ν).comp (measurable_id.sub measurable_const)).div
      (measurable_conditionedH_ref ν)) measurable_const

section
variable (B : Measure BrownianPath) [SFinite B] (hB : IsBrownianReal (fun t p => p t) B) (ν z : ℝ)
  (hν : 0 < ν) (hz : 0 < z)
include hB hz

/-- A positive-start reference-kernel event has probability between zero and one. -/
theorem brownianUpperConditionedReferenceFutureKernel_real_bounds
    (C : Set (ℚ → ℝ)) :
    0 ≤ (brownianUpperConditionedReferenceFutureKernel B ν hν z).real C ∧
      (brownianUpperConditionedReferenceFutureKernel B ν hν z).real C ≤ 1 := by
  have := isProbabilityMeasure_brownianBelowConditionedLaw B hB ν z hν hz
  have : IsProbabilityMeasure
      (brownianUpperConditionedReferenceFutureKernel B ν hν z) := by
    rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν z hν hz]
    infer_instance
  simp

/-- The positive-start reference kernel is a probability measure. -/
theorem brownianUpperConditionedReferenceFutureKernel_real_univ :
    (brownianUpperConditionedReferenceFutureKernel B ν hν z).real Set.univ = 1 := by
  have := isProbabilityMeasure_brownianBelowConditionedLaw B hB ν z hν hz
  have : IsProbabilityMeasure
      (brownianUpperConditionedReferenceFutureKernel B ν hν z) := by
    rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν z hν hz]
    infer_instance
  simp

end

/-- The real mass of a measurable event under the reference kernel is measurable in its start. -/
theorem measurable_brownianUpperConditionedReferenceFutureKernel_real
    (B : Measure BrownianPath) [SFinite B]
    (ν : ℝ) (hν : 0 < ν) (C : Set (ℚ → ℝ)) (hC : MeasurableSet C) :
    Measurable (fun z : ℝ =>
      (brownianUpperConditionedReferenceFutureKernel B ν hν z).real C) := by
  change Measurable (fun z : ℝ => ENNReal.toReal
    ((brownianUpperConditionedReferenceFutureKernel B ν hν z) C))
  exact ENNReal.measurable_toReal.comp
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
  have hds := brownianFirstHitElapsed_positiveOffsets hoff hmono
  let M  :=
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
  have hq1 : q ≤ 1 := measureReal_le_one
  let hit (m k : ℕ) := conditionedPositiveHistoryHitsOnInterval
    (dyadicLastExitCellStartTime m k) (dyadicLastExitCellEndTime m k) c
  let endpoint (m k : ℕ) := conditionedPositiveStateAt (dyadicLastExitCellEndTime m k)
  let z (m k : ℕ) (p : BrownianPath) := endpoint m k p - c
  let w (m k : ℕ) (p : BrownianPath) := lastExitAvoidanceFactor ν (c : ℝ) (endpoint m k p)
  let K (D : Set (ℚ → ℝ)) (x : ℝ) := (brownianUpperConditionedReferenceFutureKernel B ν hν x).real D
  let mix (D : Set (ℚ → ℝ)) (m k : ℕ) := ∫ p in hit m k, w m k p * K D (z m k p) ∂P
  have hcell D (hD : MeasurableSet D) m k :
      mix D m k = P.real (dyadicLastExitCellEvent m c D k) :=
    (negativeConditionedDyadicLastExitCell_test_measure hP hB hν c hc m k D hD).symm
  have hsum D (hD : MeasurableSet D) m :
      (∑' k, mix D m k) = P.real (dyadicPositiveLastExitRationalEvent m (c : ℝ) D) :=
    (negativeConditionedDyadicLastExitEvent_measure_eq_tsum hP hB hν c hc m D hD).symm
  have hs D (hD : MeasurableSet D) m : Summable (mix D m) := by
    rw [show mix D m = fun k => P.real (dyadicLastExitCellEvent m c D k) from funext (hcell D hD m)]
    simp_rw [measureReal_def]
    apply ENNReal.summable_toReal
    rw [← measure_iUnion (pairwiseDisjoint_dyadicLastExitCellEvent m c D)
      (measurableSet_dyadicLastExitCellEvent m c D hD)]
    exact measure_ne_top _ _
  have htotal m : (∑' k, mix univ m k) = 1 := by
    rw [hsum univ MeasurableSet.univ]
    simp [dyadicPositiveLastExitRationalEvent]
  have hHit (m k : ℕ) : MeasurableSet (hit m k) := by
    refine (show conditionedPositiveNaturalFiltration _ ≤ ContinuousMap.measurableSpace from
      iSup_le fun s => iSup_le fun _ => (measurable_conditionedPositiveProcessValue s).comap_le)
      _ (measurableSet_conditionedPositiveHistoryHitsOnInterval _ _ _)
  have hw m k p : 0 ≤ w m k p ∧ w m k p ≤ 1 := lastExitAvoidanceFactor_bounds hν hc
  have hwzero m k p (hz : ¬ 0 < z m k p) : w m k p = 0 := by
    have he : ¬ c < endpoint m k p := fun h => hz (sub_pos.mpr h)
    simp [w, lastExitAvoidanceFactor, he]
  have hK (D : Set (ℚ → ℝ)) {x : ℝ} (hx : 0 < x) : 0 ≤ K D x ∧ K D x ≤ 1 :=
    brownianUpperConditionedReferenceFutureKernel_real_bounds B hB ν x hν hx D
  have hmixInt D (hD : MeasurableSet D) m k :
      Integrable (fun p => w m k p * K D (z m k p)) P := by
    have he : Measurable (endpoint m k) := measurable_conditionedPositiveStateAt _
    have hm := (measurable_lastExitAvoidanceFactor ν (c : ℝ)).comp he
    have hKm := (measurable_brownianUpperConditionedReferenceFutureKernel_real B ν hν D hD).comp
      (he.sub (measurable_const (a := (c : ℝ))))
    apply Integrable.of_bound (hm.mul hKm).aestronglyMeasurable 1
    filter_upwards [] with p
    change ‖w m k p * K D (z m k p)‖ ≤ 1
    by_cases hp : 0 < z m k p
    · obtain ⟨h₀, h₁⟩ := hK D hp
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw m k p).1 h₀)]
      exact (mul_le_of_le_one_right (hw m k p).1 h₁).trans (hw m k p).2
    · simp [hwzero m k p hp]
  have hwEq m k p : w m k p * K univ (z m k p) = w m k p := by
    by_cases hp : 0 < z m k p
    · rw [show K univ (z m k p) = 1 from
        brownianUpperConditionedReferenceFutureKernel_real_univ B hB ν _ hν hp, mul_one]
    · simp [hwzero m k p hp]
  have hwInt m k : Integrable (w m k) P :=
    (hmixInt univ MeasurableSet.univ m k).congr (ae_of_all _ (hwEq m k))
  have hweight m k : mix univ m k = ∫ p in hit m k, w m k p ∂P :=
    setIntegral_congr_fun (hHit m k) (fun p _ => hwEq m k p)
  have hkernelLimit := brownianUpperConditionedReferenceFutureKernel_real_projection_tendsto_entrance
    B hB Q ν hν hQ ncoord offsets hoff hmono A hA
  apply Metric.tendsto_nhds.2
  intro ε hε
  let e := ε / 2
  have he : 0 < e := half_pos hε
  obtain ⟨δ, hδ, hnear⟩ := exists_pos_radius_mem_nhdsWithin_zero
    (hkernelLimit.eventually (Metric.ball_mem_nhds q he))
  let D : Set (ℚ → ℝ) := {y | δ ≤ y 0}
  have hD : MeasurableSet D := measurableSet_le measurable_const (measurable_pi_apply 0)
  have hnear' x (hx : 0 < x) (hxδ : x < δ) : |K C x - q| < e :=
    by exact (show dist (K C x) q < e from hnear x hx hxδ)
  have hpoint m k p : |w m k p * K C (z m k p) - q * w m k p| ≤
      e * w m k p + w m k p * K D (z m k p) := by
    by_cases hz : 0 < z m k p
    · have hw₀ := (hw m k p).1
      have hd₀ := (hK D hz).1
      rw [mul_comm q, ← mul_sub, abs_mul, abs_of_nonneg hw₀]
      by_cases hzd : z m k p < δ
      · rw [mul_comm e]
        exact (mul_le_mul_of_nonneg_left (hnear' _ hz hzd).le hw₀).trans
          (le_add_of_nonneg_right (mul_nonneg hw₀ hd₀))
      · have hD1 : K D (z m k p) = 1 := by
          simpa only [K, D, ite_eq_left (le_of_not_gt hzd)] using
            brownianUpperConditionedReferenceFutureKernel_real_initialIci B hB ν _ δ hν hz
        rw [hD1, mul_one]
        have hCz := hK C hz
        exact (mul_le_of_le_one_right hw₀ (abs_le.mpr ⟨by linarith only [hCz.1, hq1],
          by linarith only [hCz.2, hq0]⟩)).trans (le_add_of_nonneg_left (mul_nonneg he.le hw₀))
    · simp [hwzero m k p hz]
  have hlocal m k : |mix C m k - q * mix univ m k| ≤ e * mix univ m k + mix D m k := by
    have hi := (hmixInt C hC m k).sub ((hwInt m k).const_mul q)
    have hj := ((hwInt m k).const_mul e).add (hmixInt D hD m k)
    have hle : (∫ p in hit m k, |w m k p * K C (z m k p) - q * w m k p| ∂P) ≤
        ∫ p in hit m k, (e * w m k p + w m k p * K D (z m k p)) ∂P :=
      setIntegral_mono_on hi.abs.integrableOn hj.integrableOn (hHit m k) (fun p _ => hpoint m k p)
    rw [integral_add ((hwInt m k).const_mul e).integrableOn (hmixInt D hD m k).integrableOn,
      integral_const_mul, ← hweight m k] at hle
    conv_lhs => rw [hweight, ← integral_const_mul]
    change |(∫ p in hit m k, w m k p * K C (z m k p) ∂P) -
      (∫ p in hit m k, q * w m k p ∂P)| ≤ _
    rw [← integral_sub (hmixInt C hC m k).integrableOn ((hwInt m k).const_mul q).integrableOn]
    exact abs_integral_le_integral_abs.trans hle
  have herror m : |(∑' k, mix C m k) - q| ≤ e + (∑' k, mix D m k) := by
    have hu := hs univ MeasurableSet.univ m
    have hC' := hs C hC m
    have hD' := hs D hD m
    have hd := (hC'.sub (hu.mul_left q)).abs
    calc
      _ = |∑' k, (mix C m k - q * mix univ m k)| := by
        rw [hC'.tsum_sub (hu.mul_left q), hu.tsum_mul_left, htotal, mul_one]
      _ ≤ ∑' k, |mix C m k - q * mix univ m k| := by
        exact (norm_tsum_le_tsum_norm (hC'.sub (hu.mul_left q)).norm)
      _ ≤ ∑' k, (e * mix univ m k + mix D m k) :=
        hd.tsum_le_tsum (hlocal m) ((hu.mul_left e).add hD')
      _ = _ := by rw [(hu.mul_left e).tsum_add hD', hu.tsum_mul_left, htotal, mul_one]
  have htail := tendsto_measureReal_dyadicPositiveLastExitRationalEvent_zero_eval_ge hP hB hν c hc δ hδ
  filter_upwards [htail.eventually (Iio_mem_nhds he)] with m hm
  change dist (P.real (dyadicPositiveLastExitRationalEvent m (c : ℝ) C)) q < ε
  rw [Real.dist_eq, ← hsum C hC]
  have hm' : (∑' k, mix D m k) < e := by rw [hsum D hD]; exact hm
  have hb := herror m
  dsimp only [e] at hm' hb
  linarith only [hm', hb]

end DOZZ.Proofs

end
