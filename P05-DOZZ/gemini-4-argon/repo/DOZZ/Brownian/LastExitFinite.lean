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



/-- For every positive barrier, the conditioned path hits the level and has no visits arbitrarily
late, almost surely. These are exactly the path hypotheses required by the dyadic last-exit limit. -/
theorem ae_negativeConditionedLevelHitSet_nonempty_bddAbove
    {ν : ℝ} {P B : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    ∀ᵐ p ∂P,
      ({u : ℝ≥0 | p u = -(c : ℝ)}).Nonempty ∧
        BddAbove {u : ℝ≥0 | p u = -(c : ℝ)} := by
  have negativeLevelHitAfter_nat_realMeasure_tendsto_zero : Tendsto (fun n : ℕ => P.real (negativeLevelHitAfter ((n + 1 : ℕ) : ℝ≥0) (c : ℝ))) atTop (𝓝 0) := by
    have negativeLevelHitAfter_realMeasure_le_complementAvoidance (t : ℝ≥0) (ht : 0 < (t : ℝ)) (c : ℝ≥0) (hc : 0 < (c : ℝ)) : P.real (negativeLevelHitAfter t (c : ℝ)) ≤ 1 - P.real (conditionedPositiveFutureRationalAvoidance t c) := by
      let : IsProbabilityMeasure P := hP.2.1
      have hsubset : negativeLevelHitAfter t (c : ℝ) ⊆
          (conditionedPositiveFutureRationalAvoidance t c)ᶜ ∪
            conditionedPositiveFutureAvoidanceTouchEvent t c := by
        intro p hp
        by_cases hpavoid : p ∈ conditionedPositiveFutureRationalAvoidance t c
        · right
          exact conditionedPositiveFutureAvoidance_hit_implies_touch t c p hpavoid hp
        · left
          exact hpavoid
      calc
        P.real (negativeLevelHitAfter t (c : ℝ)) ≤
            P.real ((conditionedPositiveFutureRationalAvoidance t c)ᶜ ∪
              conditionedPositiveFutureAvoidanceTouchEvent t c) :=
          measureReal_mono hsubset
        _ ≤ P.real (conditionedPositiveFutureRationalAvoidance t c)ᶜ +
              P.real (conditionedPositiveFutureAvoidanceTouchEvent t c) :=
          measureReal_union_le _ _
        _ = 1 - P.real (conditionedPositiveFutureRationalAvoidance t c) := by
          rw [((measureReal_eq_zero_iff (measure_ne_top _ _)).2 (conditionedPositiveFutureAvoidanceTouchEvent_measure_zero hP hB hν t ht c hc)), add_zero, measureReal_compl (show MeasurableSet (conditionedPositiveFutureRationalAvoidance t c) by change MeasurableSet (⋂ q : ℚ, conditionedPositiveFutureAvoidanceCoordinate t c q); exact MeasurableSet.iInter fun q => measurableSet_conditionedPositiveFutureAvoidanceCoordinate t c q), probReal_univ]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      (by simpa using ((tendsto_const_nhds : Tendsto (fun _ => (1 : ℝ)) atTop (𝓝 1)).sub ((conditionedPositiveFutureRationalAvoidance_realMeasure_tendsto_one_atTop hP hB hν c hc).comp ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop).comp (tendsto_add_atTop_nat 1)))))
      (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
      (Filter.Eventually.of_forall (fun n => negativeLevelHitAfter_realMeasure_le_complementAvoidance ((n + 1 : ℕ) : ℝ≥0) (by positivity) c hc))
  let : IsProbabilityMeasure P := hP.2.1
  let low (n : ℕ) : Set BrownianPath :=
    {p | -(p ((n + 1 : ℕ) : ℝ≥0)) ≤ (c : ℝ)}
  let emptyHit : Set BrownianPath :=
    {p | ¬ ({u : ℝ≥0 | p u = -(c : ℝ)}).Nonempty}
  let badStart : Set BrownianPath := {p | p 0 ≠ 0}
  have hstart : P badStart = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hP.2.2.1] with p hp0
    simp [badStart, hp0]
  have hemptySubset n : emptyHit ⊆ low n ∪ badStart := by
    intro p hpempty
    by_cases hp0 : p 0 = 0
    · by_cases hlow : p ∈ low n
      · exact Or.inl hlow
      · have hhigh : (c : ℝ) < -(p ((n + 1 : ℕ) : ℝ≥0)) := by
          exact lt_of_not_ge (by simpa [low] using hlow)
        let f : ℝ≥0 → ℝ := fun u => -p u
        obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc
          (a := (0 : ℝ≥0)) (b := ((n + 1 : ℕ) : ℝ≥0)) (f := f) zero_le
          (p.continuous.neg.continuousOn) ⟨(by change -(p 0) ≤ (c : ℝ); rw [hp0]; simp), hhigh.le⟩
        exact False.elim (hpempty ⟨u, (by simpa [f] using (congrArg (fun x : ℝ => -x) hfu))⟩)
    · exact Or.inr hp0
  have hemptyBound n : P.real emptyHit ≤ P.real (low n) := by
    calc
      P.real emptyHit ≤ P.real (low n ∪ badStart) := measureReal_mono (hemptySubset n)
      _ ≤ P.real (low n) + P.real badStart := measureReal_union_le _ _
      _ = P.real (low n) := by rw [(show P.real badStart = 0 by rw [measureReal_def, hstart]; simp), add_zero]
  let unboundedHit : Set BrownianPath :=
    {p | ¬ BddAbove {u : ℝ≥0 | p u = -(c : ℝ)}}
  filter_upwards [(measure_eq_zero_iff_ae_notMem.mp ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 (tendsto_nhds_unique (tendsto_const_nhds : Tendsto (fun _ => P.real emptyHit) atTop (𝓝 (P.real emptyHit))) (tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) ((conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop hP hν (c : ℝ) hc).comp ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop).comp (tendsto_add_atTop_nat 1))) (Filter.Eventually.of_forall fun _ => measureReal_nonneg) (Filter.Eventually.of_forall hemptyBound))))), (measure_eq_zero_iff_ae_notMem.mp ((measureReal_eq_zero_iff (measure_ne_top _ _)).1 (tendsto_nhds_unique (tendsto_const_nhds : Tendsto (fun _ : ℕ => P.real unboundedHit) atTop (𝓝 (P.real unboundedHit))) (tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) (negativeLevelHitAfter_nat_realMeasure_tendsto_zero) (Filter.Eventually.of_forall fun _ => measureReal_nonneg) (Filter.Eventually.of_forall (fun n => by exact measureReal_mono (by intro p hp; by_contra hnot; exact hp ((brownianPath_levelHits_bddAbove_iff p (c : ℝ)).2 ⟨n + 1, (by simpa [negativeLevelHitAfter] using hnot)⟩)) (measure_ne_top _ _)))))))] with p hpempty hpbdd
  have hnonempty : ({u : ℝ≥0 | p u = -(c : ℝ)}).Nonempty := by
    simpa [emptyHit] using hpempty
  exact ⟨hnonempty, (by simpa [unboundedHit] using hpbdd)⟩

end DOZZ.Proofs

end
