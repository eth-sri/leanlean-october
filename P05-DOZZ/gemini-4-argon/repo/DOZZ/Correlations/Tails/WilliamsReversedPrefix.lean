/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.Disintegration
public import DOZZ.Brownian.BrownianFirstHitReversalLaw

/-! The Williams prefix, reversed at its lifetime, is a last-exit stopped conditioned path.
The level is retained throughout the measure identity. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- Reverse a stopped prefix and recenter it at its marked maximum. -/
noncomputable def reverseMarkedSegment (z : ℝ × StoppedBrownianPath) :
    ℝ × StoppedBrownianPath :=
  (z.1, z.2.1, ⟨fun t => z.2.2 (z.2.1 - min t z.2.1) - z.1, by fun_prop⟩)

theorem measurable_reverseMarkedSegment : Measurable reverseMarkedSegment := by
  exact measurable_fst.prodMk (measurable_snd.fst.prodMk
    (continuous_brownianPath_reverse_recenter.measurable.comp
      ((measurable_snd.fst.prodMk measurable_fst).prodMk measurable_snd.snd)))


theorem measurable_lastExitSegment_joint :
    Measurable (fun z : ℝ × BrownianPath => negativeConditionedLastExitSegment z.1 z.2) := by
  exact measurable_negativeLastExitTime_joint.prodMk
    (continuous_stopBrownianPath.measurable.comp
      (measurable_negativeLastExitTime_joint.prodMk measurable_snd))



/-- The maximum split has an independent conditioned future and a conditioned past cut at
the last exit from the independently sampled maximum level. -/
theorem williams_reversed_joint_law
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    ν (hν : 0 < ν) (Q : Measure BrownianPath)
    (hQ : IsNegativeConditionedBrownianLaw ν Q) :
    P.map (fun p =>
      (reverseMarkedSegment
        (driftedBrownianMaximum ν p, brownianPreMaximumSegment ν p),
        brownianPostMaximumPath ν p)) =
      (((brownianMaximumReferenceLaw ν).prod Q).map
        (fun z => (z.1, negativeConditionedLastExitSegment z.1 z.2))).prod Q := by
  have reversed_williams_prefix_law : (brownianWilliamsPrefixLaw P ν).map reverseMarkedSegment = ((brownianMaximumReferenceLaw ν).prod Q).map (fun z => (z.1, negativeConditionedLastExitSegment z.1 z.2)) := by
    have maximumReference_positive_ae : ∀ᵐ m ∂brownianMaximumReferenceLaw ν, 0 < m := by
      unfold brownianMaximumReferenceLaw
      rw [ae_withDensity_iff (Measurable.ennreal_ofReal ((by fun_prop : Measurable (fun m => 2 * ν * Real.exp (-2 * ν * m))).ite (measurableSet_lt measurable_const measurable_id) measurable_const) : Measurable (fun m => ENNReal.ofReal (if 0 < m then 2 * ν * Real.exp (-2 * ν * m) else 0)))]
      filter_upwards [] with m hm
      by_contra hn
      exact hm (by rw [ite_eq_right_iff.mpr (fun h => (hn h).elim), ENNReal.ofReal_zero])
    have reverse_firstHitSegment ν m p : reverseMarkedSegment (m, positiveDriftFirstHitSegment ν m p) = (m, reversedPositiveFirstHitSegment ν m p) := by
      refine Prod.ext rfl (Prod.ext rfl ?_)
      apply ContinuousMap.ext
      intro t
      change (driftedBrownianPath ν p)
          (min (firstPassageTime (driftedBrownianPath ν p) m -
            min t (firstPassageTime (driftedBrownianPath ν p) m))
            (firstPassageTime (driftedBrownianPath ν p) m)) - m = _
      rw [min_eq_left (tsub_le_self)]
      rfl
    let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
    let : IsProbabilityMeasure Q := hQ.2.1
    let : IsProbabilityMeasure (brownianMaximumReferenceLaw ν) :=
      isProbabilityMeasure_brownianMaximumReferenceLaw hν
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map hF measurable_reverseMarkedSegment]
    have hcomp : Measurable (fun z => F (reverseMarkedSegment z)) :=
      hF.comp measurable_reverseMarkedSegment
    rw [lintegral_brownianWilliamsPrefixLaw P hB ν _ hcomp,
      lintegral_map hF (measurable_fst.prodMk measurable_lastExitSegment_joint)]
    have hlast : Measurable (fun z : ℝ × BrownianPath =>
        F (z.1, negativeConditionedLastExitSegment z.1 z.2)) :=
      hF.comp (measurable_fst.prodMk measurable_lastExitSegment_joint)
    rw [lintegral_prod _ hlast.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [maximumReference_positive_ae] with m hm
    simp_rw [reverse_firstHitSegment]
    have hlaw := (brownian_firstHit_reversal_law ν m hν hm P hB Q hQ).2.2
    have ht : Measurable (fun u => F (m,u)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_map ht (measurable_reversedPositiveFirstHitSegment ν m),
      hlaw, lintegral_map ht (measurable_negativeConditionedLastExitSegment m)]
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let : IsProbabilityMeasure Q := hQ.2.1
  let : IsProbabilityMeasure (brownianWilliamsPrefixLaw P ν) :=
    isProbabilityMeasure_brownianWilliamsPrefixLaw P hB ν hν
  calc
    _ = (P.map (fun p =>
        ((driftedBrownianMaximum ν p, brownianPreMaximumSegment ν p),
          brownianPostMaximumPath ν p))).map
        (Prod.map reverseMarkedSegment id) :=
      (AEMeasurable.map_map_of_aemeasurable (measurable_reverseMarkedSegment.prodMap measurable_id).aemeasurable (((aemeasurable_driftedBrownianMaximum P hB ν hν).prodMk (aemeasurable_brownianPreMaximumSegment P hB ν hν)).prodMk (aemeasurable_brownianPostMaximumPath P hB ν hν))).symm
    _ = ((brownianWilliamsPrefixLaw P ν).prod Q).map
        (Prod.map reverseMarkedSegment id) := by
      rw [brownianPath_williams_joint_map P hB ν hν Q hQ]
    _ = ((brownianWilliamsPrefixLaw P ν).map reverseMarkedSegment).prod Q := by
      rw [← Measure.map_prod_map _ _ measurable_reverseMarkedSegment measurable_id,
        Measure.map_id]
    _ = _ := by rw [reversed_williams_prefix_law]


end DOZZ.Proofs
