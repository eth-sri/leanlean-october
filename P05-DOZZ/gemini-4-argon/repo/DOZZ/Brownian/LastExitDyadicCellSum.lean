/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitDyadicCellFormula
public import DOZZ.Brownian.LastExitDyadicIntegral
public import DOZZ.Brownian.LastExitPostPathMeasurability

/-!
# Summing the deterministic dyadic last-exit cells

The dyadic cells partition the last-exit time. On each cell, the selected endpoint is deterministic,
so the measurable rational-future event is the corresponding cell event. This module sums the
cell formula over the countable partition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped NNReal

namespace DOZZ.Proofs

/-- The path at the dyadic right endpoint, with the barrier level added back. -/
noncomputable def dyadicLastExitPathApproximation (n : ℕ) (c : ℝ) (p : BrownianPath) :
    BrownianPath :=
  shiftPathAddConstant c
    (dyadicLastExitCeilingTime n (negativeLastExitTime p c), p)

/-- The positive-coordinate rational evaluations of the dyadic post-last-exit approximation. -/
noncomputable def dyadicPositiveLastExitRationalEvals
    (n : ℕ) (c : ℝ) (p : BrownianPath) : ℚ → ℝ :=
  fun r => -brownianPathRationalEvals (dyadicLastExitPathApproximation n c p) r

/-- The test event for the selected dyadic endpoint. -/
def dyadicPositiveLastExitRationalEvent
    (n : ℕ) (c : ℝ) (C : Set (ℚ → ℝ)) : Set BrownianPath :=
  {p | dyadicPositiveLastExitRationalEvals n c p ∈ C}


theorem measurable_dyadicPositiveLastExitRationalEvals n c :
    Measurable (dyadicPositiveLastExitRationalEvals n c) := by
  apply measurable_pi_iff.mpr
  intro r
  exact ((measurable_pi_apply r).comp (measurable_brownianPathRationalEvals.comp ((by exact (continuous_shiftPathAddConstant c).measurable.comp (((measurable_dyadicLastExitCeilingTime n).comp (measurable_negativeLastExitTime_joint.comp ((measurable_const (a := c)).prodMk measurable_id))).prodMk measurable_id))))).neg


/-- The time-cell event is exactly membership of the last-exit time in the corresponding dyadic
floor cell. -/
theorem negativeConditionedLastExitTimeCell_iff_dyadicLastExitCell
    n k (c : ℝ≥0) p :
    p ∈ negativeConditionedLastExitTimeCell
        (dyadicLastExitCellStartTime n k) (dyadicLastExitCellEndTime n k) c ↔
      negativeLastExitTime p (c : ℝ) ∈ dyadicLastExitCell n k := by
  change negativeLastExitTime p (c : ℝ) ∈
      Set.Ico (dyadicLastExitCellStartTime n k) (dyadicLastExitCellEndTime n k) ↔ _
  rw [mem_dyadicLastExitCell_iff_interval]
  change (dyadicLastExitCellStartTime n k ≤ negativeLastExitTime p (c : ℝ) ∧
      negativeLastExitTime p (c : ℝ) < dyadicLastExitCellEndTime n k) ↔
    ((k : ℝ) / (2 : ℝ) ^ n ≤ (negativeLastExitTime p (c : ℝ) : ℝ) ∧
      (negativeLastExitTime p (c : ℝ) : ℝ) <
        ((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n)
  simp only [dyadicLastExitCellStartTime, dyadicLastExitCellEndTime]
  norm_cast


def dyadicLastExitCellEvent (n : ℕ) (c : ℝ≥0) (C : Set (ℚ → ℝ))
    (k : ℕ) : Set BrownianPath :=
  negativeConditionedLastExitTimeCell
      (dyadicLastExitCellStartTime n k) (dyadicLastExitCellEndTime n k) c ∩
    dyadicLastExitCellFutureEvent n k c C

/-- The selected-endpoint test event is the disjoint union of its dyadic last-exit cell events. -/
theorem iUnion_dyadicLastExitCellEvent
    n (c : ℝ≥0) (C : Set (ℚ → ℝ)) :
    (⋃ k, dyadicLastExitCellEvent n c C k) =
      dyadicPositiveLastExitRationalEvent n (c : ℝ) C := by
  have dyadicLastExitCellFutureEvent_iff_selected k (c : ℝ≥0) C p (hcell : p ∈ negativeConditionedLastExitTimeCell (dyadicLastExitCellStartTime n k) (dyadicLastExitCellEndTime n k) c) : p ∈ dyadicLastExitCellFutureEvent n k c C ↔ p ∈ dyadicPositiveLastExitRationalEvent n (c : ℝ) C := by
    change lastExitRationalShift (c : ℝ)
        (conditionedPositiveFutureRationalEvals (dyadicLastExitCellEndTime n k) p) ∈ C ↔ _
    change _ ↔ dyadicPositiveLastExitRationalEvals n (c : ℝ) p ∈ C
    exact Iff.of_eq (congrArg (fun y : ℚ → ℝ => y ∈ C) (by funext r; simp [dyadicPositiveLastExitRationalEvals, dyadicLastExitPathApproximation, brownianPathRationalEvals, shiftPathAddConstant, (show dyadicLastExitCeilingTime n (negativeLastExitTime p (c : ℝ)) = dyadicLastExitCellEndTime n k by rw [dyadicLastExitCeilingTime_eq_of_mem_cell n k _ ((negativeConditionedLastExitTimeCell_iff_dyadicLastExitCell n k c p).mp hcell)]; rfl), lastExitRationalShift, conditionedPositiveFutureRationalEvals, conditionedPositiveFuturePath]; ring)).symm
  ext p
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨k, hk⟩
    exact (dyadicLastExitCellFutureEvent_iff_selected k c C p hk.1).mp hk.2
  · intro hp
    rw [Set.mem_iUnion]
    let L := negativeLastExitTime p (c : ℝ)
    let k := Nat.floor ((L : ℝ) * (2 : ℝ) ^ n)
    refine ⟨k, ?_⟩
    have hcell : p ∈ negativeConditionedLastExitTimeCell
        (dyadicLastExitCellStartTime n k) (dyadicLastExitCellEndTime n k) c :=
      (negativeConditionedLastExitTimeCell_iff_dyadicLastExitCell n k c p).mpr (by simp [L, k, dyadicLastExitCell])
    exact ⟨hcell,
      (dyadicLastExitCellFutureEvent_iff_selected k c C p hcell).mpr hp⟩

/-- The dyadic last-exit cell events are pairwise disjoint. -/
theorem pairwiseDisjoint_dyadicLastExitCellEvent
    n (c : ℝ≥0) C :
    Pairwise (Disjoint on dyadicLastExitCellEvent n c C) := by
  intro k j hne
  change Disjoint (dyadicLastExitCellEvent n c C k)
    (dyadicLastExitCellEvent n c C j)
  rw [Set.disjoint_left]
  intro p hp hp'
  have hk := (negativeConditionedLastExitTimeCell_iff_dyadicLastExitCell
    n k c p).mp hp.1
  have hj := (negativeConditionedLastExitTimeCell_iff_dyadicLastExitCell
    n j c p).mp hp'.1
  change Nat.floor ((negativeLastExitTime p (c : ℝ) : ℝ) * (2 : ℝ) ^ n) = k at hk
  change Nat.floor ((negativeLastExitTime p (c : ℝ) : ℝ) * (2 : ℝ) ^ n) = j at hj
  exact hne (hk.symm.trans hj)

theorem measurableSet_dyadicLastExitCellEvent
    n (c : ℝ≥0) C (hC : MeasurableSet C)
    k : MeasurableSet (dyadicLastExitCellEvent n c C k) := by
  apply (measurableSet_negativeConditionedLastExitTimeCell
    (dyadicLastExitCellStartTime n k) (dyadicLastExitCellEndTime n k) c).inter
  exact measurableSet_dyadicLastExitCellFutureEvent n k c C hC

/-- The full dyadic partition turns the last-exit law into a countable sum of deterministic-time
kernel cell integrals. -/
theorem negativeConditionedDyadicLastExitEvent_measure_eq_tsum
    {ν} {P B : Measure BrownianPath} [IsFiniteMeasure P] [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (c : ℝ≥0) (hc : 0 < (c : ℝ))
    n C (hC : MeasurableSet C) :
    P.real (dyadicPositiveLastExitRationalEvent n (c : ℝ) C) =
      ∑' k, ∫ p in conditionedPositiveHistoryHitsOnInterval
          (dyadicLastExitCellStartTime n k) (dyadicLastExitCellEndTime n k) c,
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt
          (dyadicLastExitCellEndTime n k) p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt (dyadicLastExitCellEndTime n k) p - c)).real C
          ∂P := by
  let E := dyadicLastExitCellEvent n c C
  calc
    P.real (dyadicPositiveLastExitRationalEvent n (c : ℝ) C) =
        (P (⋃ k, E k)).toReal := by
      rw [← (iUnion_dyadicLastExitCellEvent n c C), measureReal_def]
    _ = (∑' k, P (E k)).toReal := by rw [measure_iUnion (pairwiseDisjoint_dyadicLastExitCellEvent n c C) (fun k => measurableSet_dyadicLastExitCellEvent n c C hC k)]
    _ = ∑' k, P.real (E k) :=
      ENNReal.tsum_toReal_eq (fun k => measure_ne_top P (E k))
    _ = ∑' k, ∫ p in conditionedPositiveHistoryHitsOnInterval
          (dyadicLastExitCellStartTime n k) (dyadicLastExitCellEndTime n k) c,
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt
          (dyadicLastExitCellEndTime n k) p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt (dyadicLastExitCellEndTime n k) p - c)).real C
          ∂P := by
      apply tsum_congr
      intro k
      exact negativeConditionedDyadicLastExitCell_test_measure
        hP hB hν c hc n k C hC

end DOZZ.Proofs

end
