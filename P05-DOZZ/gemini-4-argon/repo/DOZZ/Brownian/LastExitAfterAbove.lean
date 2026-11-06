/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitFinite
public import DOZZ.Brownian.LastExitEntranceTail
import Mathlib.Topology.Basic

/-!
# The conditioned path stays above the barrier after its last exit

The entrance state escapes every fixed lower interval in probability at deterministic integer
times. Thus it cannot stay below a fixed level forever. Combined with continuity and the finite
last-exit property, this determines the side of the barrier occupied after the last exit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- The positive coordinate lies below `c` at all sufficiently late positive integer times. -/
def conditionedPositiveEventuallyBelow (c : ℝ) : Set BrownianPath :=
  {p | ∃ N : ℕ, ∀ n : ℕ, N ≤ n → -(p ((n + 1 : ℕ) : ℝ≥0)) ≤ c}

private def conditionedPositiveBelowAfter (c : ℝ) (N : ℕ) : Set BrownianPath :=
  {p | ∀ n : ℕ, N ≤ n → -(p ((n + 1 : ℕ) : ℝ≥0)) ≤ c}


/-- Almost surely, every time strictly after the last visit to `-c` has positive coordinate
strictly above `c`. The proof uses only deterministic-time tails and path continuity. -/
theorem ae_negativeConditionedPath_above_after_lastExit
    {ν : ℝ} {P B : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    ∀ᵐ p ∂P, ∀ t : ℝ≥0,
      negativeLastExitTime p (c : ℝ) < t → (c : ℝ) < -(p t) := by
  have conditionedPositiveEventuallyBelow_measure_zero c (hc : 0 < c) : P (conditionedPositiveEventuallyBelow c) = 0 := by
    let : IsProbabilityMeasure P := hP.2.1
    have hzero N : P (conditionedPositiveBelowAfter c N) = 0 := by
      exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (tendsto_nhds_unique tendsto_const_nhds (tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds : Tendsto (fun _ => (0 : ℝ)) atTop (𝓝 0)) ((conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop hP hν c hc).comp ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop).comp (tendsto_add_atTop_nat 1))) (Filter.Eventually.of_forall fun _ => measureReal_nonneg) (by filter_upwards [eventually_ge_atTop N] with n hn; exact measureReal_mono (fun p hp => hp n hn))))
    simpa [(show conditionedPositiveEventuallyBelow c = ⋃ N : ℕ, conditionedPositiveBelowAfter c N by ext p; simp [conditionedPositiveEventuallyBelow, conditionedPositiveBelowAfter])] using (measure_iUnion_null hzero)
  filter_upwards [(ae_negativeConditionedLevelHitSet_nonempty_bddAbove hP hB hν c hc), (measure_eq_zero_iff_ae_notMem.mp (conditionedPositiveEventuallyBelow_measure_zero (c : ℝ) hc))] with p hp hpn
  rcases hp with ⟨hnonempty, hbounded⟩
  have hnohit : ∀ u : ℝ≥0, negativeLastExitTime p (c : ℝ) < u →
      p u ≠ -(c : ℝ) := by
    intro u hu hpu
    exact (not_le_of_gt hu) (le_csSup hbounded hpu)
  intro t ht
  by_contra hnot
  obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
  have hEventually : p ∈ conditionedPositiveEventuallyBelow (c : ℝ) := by
    refine ⟨N, fun n hn => ?_⟩
    let T := ((n + 1 : ℕ) : ℝ≥0)
    by_contra hT
    let f : ℝ≥0 → ℝ := fun s => -(p s)
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc
      (a := t) (b := T) (f := f) (by apply NNReal.coe_le_coe.mp; dsimp [T]; exact hN.le.trans (by exact_mod_cast Nat.le_trans hn (Nat.le_succ n))) p.continuous.neg.continuousOn
      ⟨(show -(p t) < (c : ℝ) by by_contra heq; exact hnohit t ht (by linarith)).le, (lt_of_not_ge hT).le⟩
    exact hnohit u (lt_of_lt_of_le ht hu.1) (by simpa [f] using (congrArg (fun x : ℝ => -x) hfu))
  exact hpn hEventually

end DOZZ.Proofs

end
