module

public import PottsDiscontinuity.Torus.LoopHomology
public import PottsDiscontinuity.Torus.LoopTurning

/-! # The discrete rotation sum is divisible by one full turn -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The four cardinal directions as elements of the discrete angle group. -/
def portAngle : Port → ZMod 4
  | .east => 0
  | .north => 1
  | .west => 2
  | .south => 3

/-- The direction opposite to an incident port. -/
def oppositePort : Port → Port
  | .west => .east
  | .east => .west
  | .south => .north
  | .north => .south

private theorem strandTurn_pair_angle (b : Bool) (p : Port) :
    (strandTurn b (pairedPort b (oppositePort p)) : ZMod 4) =
      portAngle (pairedPort b (oppositePort p)) - portAngle p := by
  cases b <;> cases p <;> decide

variable (ω : ArrowConfig N M) (s : Smoothing N M)

/-- At one step of the directed loop, the local turn is the change of direction modulo a full turn. -/
theorem strandTurn_step_angle (d : Dart N M) :
    (strandTurn (s (stepPerm s d).1) (stepPerm s d).2 : ZMod 4) =
      portAngle (stepPerm s d).2 - portAngle d.2 := by
  rw [stepPerm_apply, strandReverse]
  rcases d with ⟨v, p⟩
  have he : (edgeReverse (v, p)).2 = oppositePort p := by
    cases p <;> rfl
  rw [he]
  exact strandTurn_pair_angle (s (edgeReverse (v, p)).1) p

/-- Every directed loop has an integral discrete rotation number modulo four turns. -/
theorem loopTurn_mod_four
    (h : CompatibleConfig ω s) (q : DirectedLoop h) :
    (loopTurn q : ZMod 4) = 0 := by
  classical
  have hstep := loopSum_step (fun d => strandTurn (s d.1) d.2) q
  have hcast :
      (loopTurn q : ZMod 4) =
        (loopSum (fun d => strandTurn (s (stepPerm s d).1)
          (stepPerm s d).2) q : ZMod 4) := by
    exact congrArg (fun z : ℤ => (z : ZMod 4)) hstep.symm
  have hlocal :
      (loopSum (fun d => strandTurn (s (stepPerm s d).1)
        (stepPerm s d).2) q : ZMod 4) =
        ∑ d : DirectedDart ω,
          if directedLoopOf h d = q then
            portAngle (stepPerm s d.val).2 - portAngle d.val.2 else 0 := by
    unfold loopSum
    simp only [Finset.sum_filter, Int.cast_sum, Int.cast_ite, Int.cast_zero]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : directedLoopOf h d = q
    · simp [hd]
      exact strandTurn_step_angle s d.val
    · grind
  have hangle :
      (∑ d : DirectedDart ω,
        if directedLoopOf h d = q then portAngle (stepPerm s d.val).2 else 0) =
      ∑ d : DirectedDart ω,
        if directedLoopOf h d = q then portAngle d.val.2 else 0 := by
    let g := fun d =>
      if directedLoopOf h d = q then portAngle d.val.2 else 0
    calc
      _ = ∑ d : DirectedDart ω, g (directedStep h d) := by
        apply Finset.sum_congr rfl
        simp [g, directedLoopOf_step]
      _ = ∑ d : DirectedDart ω, g d := Equiv.sum_comp (directedStep h) g
      _ = _ := by rfl
  have hdiff :
      (∑ d : DirectedDart ω,
        if directedLoopOf h d = q then
          portAngle (stepPerm s d.val).2 - portAngle d.val.2 else 0) = 0 := by
    have hsplit : (∑ d : DirectedDart ω,
        if directedLoopOf h d = q then
          portAngle (stepPerm s d.val).2 - portAngle d.val.2 else 0) =
      (∑ d : DirectedDart ω,
        if directedLoopOf h d = q then portAngle (stepPerm s d.val).2 else 0) -
      (∑ d : DirectedDart ω,
        if directedLoopOf h d = q then portAngle d.val.2 else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : directedLoopOf h d = q <;> simp [hd]
    rw [hsplit, hangle, sub_self]
  rw [hcast, hlocal, hdiff]

end PottsDiscontinuity.Torus
