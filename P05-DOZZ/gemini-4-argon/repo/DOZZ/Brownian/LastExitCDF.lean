/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitAfterAbove

/-!
# The deterministic-time last-exit distribution identity

The last exit is at most a deterministic time precisely when the future avoids the level.
The full-history avoidance identity therefore gives the conditional last-exit distribution.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace DOZZ.Proofs



/-- The last-exit CDF factors against every event in the deterministic-time history. -/
theorem conditionedPositiveHistory_lastExit_le_setIntegral
    {ν : ℝ} {P B : Measure BrownianPath} [IsFiniteMeasure P] [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (t c : ℝ≥0)
    (ht : 0 < (t : ℝ)) (hc : 0 < (c : ℝ))
    A
    (hA : MeasurableSet[conditionedPositiveNaturalFiltration t] A) :
    (∫ p in A, ({p : BrownianPath | negativeLastExitTime p (c : ℝ) ≤ t}).indicator
      (fun _ => (1 : ℝ)) p ∂P) =
      ∫ p in A, lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) ∂P := by
  have conditionedPositiveHistory_condExp_lastExit_le : P[({p : BrownianPath | negativeLastExitTime p (c : ℝ) ≤ t}).indicator (fun _ => (1 : ℝ)) | conditionedPositiveNaturalFiltration t] =ᵐ[P] fun p => lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) := by
    have negativeLastExitTime_le_ae_eq_futureAvoidance : {p : BrownianPath | negativeLastExitTime p (c : ℝ) ≤ t} =ᵐ[P] conditionedPositiveFutureRationalAvoidance t c := by
      filter_upwards [(ae_negativeConditionedLevelHitSet_nonempty_bddAbove hP hB hν c hc), (ae_negativeConditionedPath_above_after_lastExit hP hB hν c hc), (measure_eq_zero_iff_ae_notMem.mp (conditionedPositiveFutureAvoidanceTouchEvent_measure_zero hP hB hν t ht c hc))] with p hp hafter hnt
      apply propext
      constructor
      · intro hL
        simp only [conditionedPositiveFutureRationalAvoidance, Set.mem_iInter]
        intro q
        by_cases hq : 0 < (q : ℝ)
        · rw [conditionedPositiveFutureAvoidanceCoordinate, dite_eq_left hq]
          let qTime : ℝ≥0 := ⟨(q : ℝ), hq.le⟩
          simpa [conditionedPositiveFutureRationalEvals, conditionedPositiveFuturePath,
            conditionedPositiveStateAt, qTime, max_eq_left hq.le] using (hafter (t + qTime) (lt_of_le_of_lt hL (lt_add_of_pos_right t hq)))
        · simp [conditionedPositiveFutureAvoidanceCoordinate, hq]
      · intro havoid
        apply (negativeLastExitTime_le_iff_no_future_visit p (c : ℝ) t hp.2).mpr
        intro u htu hpu
        exact hnt (conditionedPositiveFutureAvoidance_hit_implies_touch t c p havoid
          ⟨u, htu, hpu⟩)
    have hind : ({p : BrownianPath | negativeLastExitTime p (c : ℝ) ≤ t}).indicator
        (fun _ => (1 : ℝ)) =ᵐ[P]
        (conditionedPositiveFutureRationalAvoidance t c).indicator (fun _ => (1 : ℝ)) := by
      filter_upwards [(negativeLastExitTime_le_ae_eq_futureAvoidance)] with p hp
      by_cases hL : negativeLastExitTime p (c : ℝ) ≤ t
      · have ha : p ∈ conditionedPositiveFutureRationalAvoidance t c := hp ▸ hL
        simp [hL, ha]
      · have ha : p ∉ conditionedPositiveFutureRationalAvoidance t c := hp ▸ hL
        simp [hL, ha]
    exact (condExp_congr_ae hind).trans
      (conditionedPositiveHistory_condExp_rationalFuture_avoidance_probability
        hP B hB t ht hν c hc)
  have hm : conditionedPositiveNaturalFiltration t ≤ ContinuousMap.measurableSpace := by
    refine iSup_le fun s => iSup_le fun _ => ?_
    exact (measurable_conditionedPositiveProcessValue s).comap_le
  calc
    _ = ∫ p in A, P[({p : BrownianPath | negativeLastExitTime p (c : ℝ) ≤ t}).indicator
        (fun _ => (1 : ℝ)) | conditionedPositiveNaturalFiltration t] p ∂P :=
      (setIntegral_condExp hm ((integrable_const (1 : ℝ)).indicator (measurableSet_le (measurable_negativeLastExitTime_joint.comp (measurable_const.prodMk measurable_id)) measurable_const)) hA).symm
    _ = _ := setIntegral_congr_ae (hm A hA)
      ((conditionedPositiveHistory_condExp_lastExit_le).mono
        fun p hp _ => hp)

end DOZZ.Proofs

end
