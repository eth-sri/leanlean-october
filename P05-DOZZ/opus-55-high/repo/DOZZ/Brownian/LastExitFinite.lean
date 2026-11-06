/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitAvoidanceTouch
public import DOZZ.Brownian.LastExitAvoidanceProbabilityLimit
public import DOZZ.Brownian.LastExitAvoidance
public import DOZZ.Brownian.Williams.StoppedPaths

/-!
# Finite nonempty level-hit sets for the conditioned entrance path

The rational survival probability tends to one at large deterministic times. Atomlessness removes
the possible rational-survival tangency, so visits after a deterministic time have probability at
most the survival complement. This proves the level-hit set is bounded. The one-time tail and
continuity from the entrance value prove it is nonempty.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- A visit to `-c` strictly after deterministic time `t`. -/
def negativeLevelHitAfter (t : ℝ≥0) (c : ℝ) : Set BrownianPath :=
  {p | ∃ u : ℝ≥0, t < u ∧ p u = -c}
section
variable {ν : ℝ} {P B : Measure BrownianPath} [SFinite B] (hP : IsNegativeConditionedBrownianLaw ν P) (hB : IsBrownianReal (fun t p => p t) B) (hν : 0 < ν)
include hP hB hν

/-- The probability of a future visit is bounded by the probability that strict rational
avoidance fails. -/
theorem negativeLevelHitAfter_realMeasure_le_complementAvoidance
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    P.real (negativeLevelHitAfter t (c : ℝ)) ≤
      1 - P.real (conditionedPositiveFutureRationalAvoidance t c) := by
  let : IsProbabilityMeasure P := hP.2.1
  have havoid : MeasurableSet (conditionedPositiveFutureRationalAvoidance t c) := by
    change MeasurableSet (⋂ q : ℚ,
      conditionedPositiveFutureAvoidanceCoordinate t c q)
    exact MeasurableSet.iInter fun q =>
      measurableSet_conditionedPositiveFutureAvoidanceCoordinate t c q
  have hHitMeas : MeasurableSet (negativeLevelHitAfter t c) := by
    change MeasurableSet ((fun p => ((c : ℝ), p)) ⁻¹'
      {z : ℝ × BrownianPath | ∃ u : ℝ≥0, t < u ∧ z.2 u = -z.1})
    exact (measurableSet_brownianPath_levelHit_after t).preimage
      (measurable_const.prodMk measurable_id)
  have hTouch := conditionedPositiveFutureAvoidanceTouchEvent_measure_zero
    hP hB hν t ht c hc
  have hTouchReal :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).2 hTouch
  have hsubset : negativeLevelHitAfter t c ⊆
      (conditionedPositiveFutureRationalAvoidance t c)ᶜ ∪
        conditionedPositiveFutureAvoidanceTouchEvent t c := by
    intro p hp
    by_cases hpavoid : p ∈ conditionedPositiveFutureRationalAvoidance t c
    · right
      exact conditionedPositiveFutureAvoidance_hit_implies_touch t c p hpavoid hp
    simp_all
  calc
    P.real _ ≤
        P.real ((conditionedPositiveFutureRationalAvoidance t c)ᶜ ∪
          conditionedPositiveFutureAvoidanceTouchEvent t c) :=
      measureReal_mono hsubset
    _ ≤ P.real _ᶜ +
          P.real _ :=
      measureReal_union_le ..
    _ = 1 - P.real _ := by
      rw [hTouchReal, add_zero, measureReal_compl havoid, probReal_univ]
section
variable (c : ℝ≥0) (hc : 0 < (c : ℝ))
include hc

/-- Visits after large deterministic times have probability tending to zero. -/
theorem negativeLevelHitAfter_nat_realMeasure_tendsto_zero
    :
    Tendsto (fun n : ℕ =>
      P.real (negativeLevelHitAfter ((n + 1 : ℕ) : ℝ≥0) (c : ℝ))) atTop (𝓝 0) := by
  have htime : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
  have hsurv :=
    (conditionedPositiveFutureRationalAvoidance_realMeasure_tendsto_one_atTop
      hP hB hν c hc).comp htime
  have hcomplement : Tendsto (fun n : ℕ =>
      1 - P.real (conditionedPositiveFutureRationalAvoidance
        ((n + 1 : ℕ) : ℝ≥0) c))
      atTop (𝓝 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ => (1 : ℝ)) atTop (𝓝 1)).sub hsurv)
  have hbound (n : ℕ) :
      P.real (negativeLevelHitAfter ((n + 1 : ℕ) : ℝ≥0) (c : ℝ)) ≤
        1 - P.real (conditionedPositiveFutureRationalAvoidance
          ((n + 1 : ℕ) : ℝ≥0) c) := by
    exact negativeLevelHitAfter_realMeasure_le_complementAvoidance
      hP hB hν ((n + 1 : ℕ) : ℝ≥0) (by positivity) c hc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ => (0 : ℝ)) atTop (𝓝 0))
    hcomplement
    (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
    (Filter.Eventually.of_forall hbound)

/-- For every positive barrier, the conditioned path hits the level and has no visits arbitrarily
late, almost surely. These are exactly the path hypotheses required by the dyadic last-exit limit. -/
theorem ae_negativeConditionedLevelHitSet_nonempty_bddAbove
    :
    ∀ᵐ p ∂P,
      ({u : ℝ≥0 | p u = -(c : ℝ)}).Nonempty ∧
        BddAbove {u : ℝ≥0 | p u = -(c : ℝ)} := by
  let : IsProbabilityMeasure P := hP.2.1
  have htime : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
  have htail :=
    (conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop
      hP hν (c : ℝ) hc).comp htime
  let low (n : ℕ) : Set BrownianPath :=
    {p | -(p ((n + 1 : ℕ) : ℝ≥0)) ≤ (c : ℝ)}
  let emptyHit : Set BrownianPath :=
    {p | ¬ ({u : ℝ≥0 | p u = -(c : ℝ)}).Nonempty}
  let badStart : Set BrownianPath := {p | p 0 ≠ 0}
  have hstart : P badStart = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hP.2.2.1] with p hp0
    tauto
  have hstartReal : P.real badStart = 0 := by
    rw [measureReal_def, hstart]
    simp
  have hemptySubset (n : ℕ) : emptyHit ⊆ low n ∪ badStart := by
    intro p hpempty
    by_cases hp0 : p 0 = 0
    · by_cases hlow : p ∈ low n
      · simp_all
      · have hhigh : (c : ℝ) < -(p ((n + 1 : ℕ) : ℝ≥0)) := by
          have hnot : ¬ -(p ((n + 1 : ℕ) : ℝ≥0)) ≤ (c : ℝ) := by
            simpa [low] using hlow
          exact lt_of_not_ge hnot
        let f : ℝ≥0 → ℝ := fun u => -p u
        have hf0 : f 0 ≤ (c : ℝ) := by
          change -(p 0) ≤ (c : ℝ)
          rw [hp0]
          simp
        have hfT : (c : ℝ) ≤ f ((n + 1 : ℕ) : ℝ≥0) := hhigh.le
        obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc
          (a := (0 : ℝ≥0)) zero_le
          (p.continuous.neg.continuousOn) ⟨hf0, hfT⟩
        have hhit : p u = -(c : ℝ) := by
          simpa [f] using (congrArg (fun x => -x) hfu)
        exact False.elim (hpempty ⟨u, hhit⟩)
    · exact Or.inr hp0
  have hemptyBound (n : ℕ) : P.real emptyHit ≤ P.real (low n) := by
    calc
      P.real emptyHit ≤ P.real _ := measureReal_mono (hemptySubset n)
      _ ≤ P.real (low n) + P.real badStart := measureReal_union_le ..
      _ = P.real (low n) := by linarith
  have hemptyLimit : Tendsto (fun n => P.real emptyHit) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ => (0 : ℝ)) atTop (𝓝 0))
      htail
      (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
      (Filter.Eventually.of_forall hemptyBound)
  have hemptyReal : P.real emptyHit = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds :
      Tendsto (fun _ => P.real emptyHit) atTop _) hemptyLimit
  have hempty : P emptyHit = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hemptyReal
  have hemptyAE : ∀ᵐ p ∂P, p ∉ emptyHit :=
    measure_eq_zero_iff_ae_notMem.mp hempty
  let unboundedHit : Set BrownianPath :=
    {p | ¬ BddAbove {u : ℝ≥0 | p u = -(c : ℝ)}}
  have hunboundedBound (n : ℕ) :
      P.real unboundedHit ≤
        P.real (negativeLevelHitAfter ((n + 1 : ℕ) : ℝ≥0) (c : ℝ)) := by
    have hsubset : unboundedHit ⊆
        negativeLevelHitAfter ((n + 1 : ℕ) : ℝ≥0) (c : ℝ) := by
      intro p hp
      by_contra hnot
      have hfree : ¬ ∃ u : ℝ≥0, ((n + 1 : ℕ) : ℝ≥0) < u ∧
          p u = -(c : ℝ) := by
        simpa [negativeLevelHitAfter] using hnot
      have hbdd : BddAbove {u : ℝ≥0 | p u = -(c : ℝ)} :=
        (brownianPath_levelHits_bddAbove_iff p (c : ℝ)).2 ⟨n + 1, hfree⟩
      exact hp hbdd
    exact measureReal_mono hsubset (measure_ne_top _ _)
  have hunboundedLimit : Tendsto (fun n => P.real unboundedHit) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ => (0 : ℝ)) atTop (𝓝 0))
      (negativeLevelHitAfter_nat_realMeasure_tendsto_zero hP hB hν c hc)
      (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
      (Filter.Eventually.of_forall hunboundedBound)
  have hunboundedReal : P.real unboundedHit = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds :
      Tendsto (fun _ => P.real unboundedHit) atTop _)
      hunboundedLimit
  have hunbounded : P unboundedHit = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hunboundedReal
  have hunboundedAE : ∀ᵐ p ∂P, p ∉ unboundedHit :=
    measure_eq_zero_iff_ae_notMem.mp hunbounded
  filter_upwards [hemptyAE, hunboundedAE] with p hpempty hpbdd
  have hnonempty : ({u : ℝ≥0 | p u = -(c : ℝ)}).Nonempty := by
    simpa [emptyHit] using hpempty
  have hbounded : BddAbove {u : ℝ≥0 | p u = -(c : ℝ)} := by
    simpa [unboundedHit] using hpbdd
  exact ⟨hnonempty, hbounded⟩

end

end

end DOZZ.Proofs

end
