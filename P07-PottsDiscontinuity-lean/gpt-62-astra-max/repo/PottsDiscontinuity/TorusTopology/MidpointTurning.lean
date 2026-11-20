module

public import PottsDiscontinuity.Torus.LoopRotationNumber
public import PottsDiscontinuity.Torus.RibbonCorners
public import PottsDiscontinuity.TorusTopology.LoopMidpoints

/-! Rotation-preserving transport of the actual turning sum to the lifted
square-lattice midpoint polygon. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
variable {N M : ℕ}

/-- The principal signed change of cardinal direction, in quarter turns;
for the antipodal case the principal value is +2. -/
def latticeQuarterTurn (p r : Port) : ℤ :=
  if r = p then 0 else if r = ccwPort p then 1 else if r = cwPort p then -1 else 2

private lemma midpointTurn_table (p : Port) (b c : Bool) :
    2 * latticeQuarterTurn (midpointStepPort b p)
        (midpointStepPort c (pairedPort b (oppositePort p))) =
      strandTurn b (pairedPort b (oppositePort p)) +
        strandTurn c (pairedPort c (oppositePort (pairedPort b (oppositePort p)))) := by
  cases p <;> cases b <;> cases c <;> decide

variable (ω : ArrowConfig N M) (s : Smoothing N M) (d : Dart N M) (h : CompatibleConfig ω s)
include s

include d in
/-- Direction of the actual unit lattice edge from this midpoint to the next. -/
def midpointDirection : Port :=
  midpointStepPort (s (stepPerm s d).1) d.2

include d in
/-- The actual signed turn at the next midpoint of the lifted polygon. -/
def midpointQuarterTurn : ℤ :=
  latticeQuarterTurn (midpointDirection s d) (midpointDirection s (stepPerm s d))

lemma stepPerm_port :
    (stepPerm s d).2 = pairedPort (s (stepPerm s d).1) (oppositePort d.2) := by
  rcases d with ⟨v,p⟩
  cases p <;> rfl

/-- The direction used in the turn formula is the geometric direction of the
actual lifted midpoint edge. -/
theorem loopMidpointPosition_succ_direction
    (d : DirectedDart ω) (n : ℕ) :
    loopMidpointPosition h d (n+1) = loopMidpointPosition h d n +
      portVector (midpointDirection s ((directedStep h)^[n] d).val) := by
  let e := (directedStep h)^[n] d
  unfold loopMidpointPosition
  rw [loopLiftPosition_succ]
  have hv : (horizontalIncrement e.val,verticalIncrement e.val) = portVector e.val.2 := by
    rcases e with ⟨⟨v,p⟩,he⟩
    cases p <;> rfl
  rw [show (horizontalIncrement ((directedStep h)^[n] d).val,
    verticalIncrement ((directedStep h)^[n] d).val) = portVector e.val.2 from hv]
  rw [Function.iterate_succ_apply',directedStep_val]
  rw [stepPerm_port]
  exact rotatedMidpoint_step _ _ _

/-- Midpoint turning is the average of the two adjacent original strand turns. -/
lemma two_mul_midpointQuarterTurn :
    2 * midpointQuarterTurn s d =
      strandTurn (s (stepPerm s d).1) (stepPerm s d).2 +
      strandTurn (s (stepPerm s (stepPerm s d)).1) (stepPerm s (stepPerm s d)).2 := by
  unfold midpointQuarterTurn midpointDirection
  have ht := midpointTurn_table d.2 (s (stepPerm s d).1) (s (stepPerm s (stepPerm s d)).1)
  rw [stepPerm_port s (stepPerm s d),stepPerm_port s d]
  exact ht

/-- Summing the transported turns over the genuine cycle gives the exact
quarter-turn sum `Torus.loopTurn`, including its sign. -/
theorem loopSum_midpointQuarterTurn_eq_loopTurn
    (q : DirectedLoop h) :
    loopSum (midpointQuarterTurn s) q = loopTurn q := by
  classical
  have he : 2 * loopSum (midpointQuarterTurn s) q =
      loopSum (fun d => strandTurn (s (stepPerm s d).1) (stepPerm s d).2) q +
      loopSum (fun d => strandTurn (s (stepPerm s (stepPerm s d)).1)
        (stepPerm s (stepPerm s d)).2) q := by
    unfold loopSum
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun d _ => two_mul_midpointQuarterTurn s d.val)
  have hs₁ := loopSum_step (fun d => strandTurn (s d.1) d.2) q
  have hs₂ := loopSum_step
    (fun d => strandTurn (s (stepPerm s d).1) (stepPerm s d).2) q
  rw [hs₂,hs₁] at he
  change 2 * loopSum (midpointQuarterTurn s) q = loopTurn q + loopTurn q at he
  omega

/-- The ordered polygon's total turn is exactly four times the requested
rotation number on the original quotient carrier. -/
theorem sum_period_midpointQuarterTurn_eq_four_mul_rotationNumber
    (d : DirectedDart ω) :
    (∑ k ∈ range (loopPeriod h d), midpointQuarterTurn s
      ((directedStep h)^[k] d).val) =
      4 * loopRotationNumber (directedLoopOf h d) := by
  rw [← loopSum_eq_sum_period,loopSum_midpointQuarterTurn_eq_loopTurn]
  exact loopTurn_eq_four_mul_rotationNumber ω s h _

end PottsDiscontinuity.TorusTopology
