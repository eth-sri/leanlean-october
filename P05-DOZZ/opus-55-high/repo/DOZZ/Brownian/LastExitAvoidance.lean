/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeLastExitTime
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Deterministic-time characterization of a last exit

The last-exit distribution is obtained by asking whether the future visits the level after a
deterministic time. This order-theoretic lemma isolates that event identity; probabilistic
conditioning is then applied at the deterministic time, never at the last exit itself.
-/

@[expose] public section

open Set
open Filter Topology
open scoped NNReal

namespace DOZZ.Proofs
section
variable (p : BrownianPath) (c : ℝ)

/-- If the set of visits to `-c` is bounded, the last-exit time is at most `t` exactly when the
path does not visit `-c` at any later time. -/
theorem negativeLastExitTime_le_iff_no_future_visit
    (t : ℝ≥0)
    (hbounded : BddAbove {u : ℝ≥0 | p u = -c}) :
    negativeLastExitTime p c ≤ t ↔ ∀ u : ℝ≥0, t < u → p u ≠ -c := by
  rw [negativeLastExitTime]
  let A := {u | p u = -c}
  by_cases hA : A.Nonempty
  · constructor
    · intro hlast u htu hu
      exact (not_lt_of_ge ((le_csSup hbounded hu).trans hlast)) htu
    · intro havoid
      apply csSup_le hA
      grind
  · have hAempty := Set.not_nonempty_iff_eq_empty.mp hA
    constructor
    · tauto
    aesop

/-- A finite last exit of a continuous path is attained. The hit set is closed, so its supremum
belongs to the set whenever it is nonempty and bounded above. -/
theorem negativeLastExitTime_mem_of_nonempty_bddAbove
    (hnonempty : ({u : ℝ≥0 | p u = -c}).Nonempty)
    (hbounded : BddAbove {u : ℝ≥0 | p u = -c}) :
    p (negativeLastExitTime p c) = -c := by
  let A := {u | p u = -c}
  have hclosed : IsClosed A := isClosed_singleton.preimage p.continuous
  exact (hclosed.csSup_mem hnonempty hbounded)

end

/-- Right endpoint of the dyadic mesh cell strictly containing a nonnegative last-exit time.
The strict upper endpoint convention avoids any ambiguity when the last exit itself is dyadic. -/
noncomputable def dyadicLastExitCeilingTime (n : ℕ) (L : ℝ≥0) : ℝ≥0 :=
  ⟨((Nat.floor ((L : ℝ) * (2 : ℝ) ^ n) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n, by positivity⟩

/-- The deterministic dyadic ceiling lies strictly after `L` and less than one mesh width
after it. Thus it converges to `L`; each ceiling is a deterministic time on its corresponding
mesh cell. -/
theorem dyadicLastExitCeilingTime_bounds (n : ℕ) (L : ℝ≥0) :
    (L : ℝ) < (dyadicLastExitCeilingTime n L : ℝ) ∧
      (dyadicLastExitCeilingTime n L : ℝ) ≤ (L : ℝ) + 1 / (2 : ℝ) ^ n := by
  let a := (2 : ℝ) ^ n
  have ha : 0 < a := by positivity
  have hfloor_le : (Nat.floor ((L : ℝ) * a) : ℝ) ≤ (L : ℝ) * a :=
    Nat.floor_le (by positivity)
  have hlt : (L : ℝ) * a < (Nat.floor ((L : ℝ) * a) : ℝ) + 1 := by
    bound
  constructor
  · change (L : ℝ) <
      ((Nat.floor ((L : ℝ) * a) + 1 : ℕ) : ℝ) / a
    push_cast
    rw [lt_div_iff₀ ha]
    exact hlt
  · change ((Nat.floor ((L : ℝ) * a) + 1 : ℕ) : ℝ) / a ≤
      (L : ℝ) + 1 / a
    rw [div_le_iff₀ ha]
    grind

/-- The deterministic dyadic ceiling times converge to the given nonnegative time. -/
theorem dyadicLastExitCeilingTime_coe_tendsto (L : ℝ≥0) :
    Tendsto (fun n : ℕ => (dyadicLastExitCeilingTime n L : ℝ)) atTop (𝓝 (L : ℝ)) := by
  have hmesh : Tendsto (fun n => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  have hupper : Tendsto (fun n => (L : ℝ) + 1 / (2 : ℝ) ^ n)
      atTop (𝓝 (L : ℝ)) := by
    simpa using tendsto_const_nhds.add hmesh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => (dyadicLastExitCeilingTime_bounds n L).1.le)
    (fun n => (dyadicLastExitCeilingTime_bounds n L).2)

/-- Evaluating a continuous path at the deterministic dyadic ceilings of its finite last exit
converges to the barrier value at the last exit. -/
theorem continuousPath_dyadicLastExitCeiling_eval_tendsto
    (p : BrownianPath) (c : ℝ)
    (hnonempty : ({u : ℝ≥0 | p u = -c}).Nonempty)
    (hbounded : BddAbove {u : ℝ≥0 | p u = -c}) :
    Tendsto
      (fun n : ℕ => p (dyadicLastExitCeilingTime n (negativeLastExitTime p c)))
      atTop (𝓝 (-c)) := by
  let L := negativeLastExitTime p c
  have hlast : p L = -c := negativeLastExitTime_mem_of_nonempty_bddAbove p c
    hnonempty hbounded
  have hL : 0 ≤ (L : ℝ) := L.property
  let F : ℝ → ℝ := fun x => p ⟨max x 0, le_max_right x 0⟩
  have hF : Continuous F := by
    fun_prop
  have hFL : F (L : ℝ) = p L := by
    aesop
  have hcomp : Tendsto (fun n => F (dyadicLastExitCeilingTime n L : ℝ))
      atTop (𝓝 (p L)) := by
    rw [← hFL]
    exact (hF.tendsto (L : ℝ)).comp (dyadicLastExitCeilingTime_coe_tendsto L)
  aesop

end DOZZ.Proofs

end
