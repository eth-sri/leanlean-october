module

public import PottsDiscontinuity.Torus.LoopTurnDivisibility
public import PottsDiscontinuity.TorusTopology.LoopLiftProjection

/-! A lattice embedding of the lifted smoothed loops. Rotating edge midpoints
through minus 45 degrees gives ordinary integer square-lattice vertices. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops TorusRC
variable {N M : ℕ}

/-- Unit vector along a port in the original medial coordinates. -/
def portVector : Port → ℤ × ℤ
  | .west => (-1,0)
  | .east => (1,0)
  | .south => (0,-1)
  | .north => (0,1)

/-- Integer coordinates of an edge midpoint after rotation and rescaling.
The fixed translation removes the half-integer offsets. -/
def rotatedMidpoint (z : ℤ × ℤ) : Port → ℤ × ℤ
  | .west => (z.1+z.2-1,z.2-z.1+1)
  | .east => (z.1+z.2,z.2-z.1)
  | .south => (z.1+z.2-1,z.2-z.1)
  | .north => (z.1+z.2,z.2-z.1+1)

/-- Midpoints identify precisely the two orientations of a geometric edge. -/
lemma rotatedMidpoint_eq_iff (z w : ℤ × ℤ) (p r : Port) :
    rotatedMidpoint z p = rotatedMidpoint w r ↔
      (z = w ∧ p = r) ∨ (w = z + portVector p ∧ r = oppositePort p) := by
  rcases z with ⟨x,y⟩
  rcases w with ⟨a,b⟩
  cases p <;> cases r <;>
    simp [rotatedMidpoint,portVector,oppositePort,Prod.ext_iff] <;> omega

/-- Direction of the segment joining consecutive edge midpoints. -/
def midpointStepPort : Bool → Port → Port
  | false,.east | false,.north => .east
  | false,.west | false,.south => .west
  | true,.east | true,.south => .south
  | true,.west | true,.north => .north

lemma rotatedMidpoint_step (z : ℤ × ℤ) (p : Port) (b : Bool) :
    rotatedMidpoint (z + portVector p) (pairedPort b (oppositePort p)) =
      rotatedMidpoint z p + portVector (midpointStepPort b p) := by
  rcases z with ⟨x,y⟩
  cases p <;> cases b <;>
    simp [rotatedMidpoint,portVector,pairedPort,oppositePort,midpointStepPort,Prod.ext_iff] <;>
    omega

/-- The actual lifted midpoint at time n in the actual directed orbit. -/
noncomputable def loopMidpointPosition (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) (n : ℕ) : ℤ × ℤ :=
  rotatedMidpoint (loopLiftPosition ω s h d n) ((directedStep ω s h)^[n] d).val.2

private lemma increment_pair (d : Dart N M) :
    (horizontalIncrement d,verticalIncrement d) = portVector d.2 := by
  rcases d with ⟨v,p⟩
  cases p <;> rfl

section

variable
  (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω)

/-- Every segment of the lifted midpoint polygon is an ordinary unit lattice edge. -/
theorem loopMidpointPosition_step (n : ℕ) :
    ∃ p : Port, loopMidpointPosition ω s h d (n+1) =
      loopMidpointPosition ω s h d n + portVector p := by
  let e := (directedStep ω s h)^[n] d
  refine ⟨midpointStepPort (s (edgeReverse e.val).1) e.val.2,?_⟩
  unfold loopMidpointPosition
  rw [loopLiftPosition_succ,increment_pair, Function.iterate_succ_apply',directedStep_val]
  change rotatedMidpoint (loopLiftPosition ω s h d n + portVector e.val.2)
    (pairedPort (s (edgeReverse e.val).1) (edgeReverse e.val).2) = _
  have hp : (edgeReverse e.val).2 = oppositePort e.val.2 := by
    rcases e with ⟨⟨v,p⟩,he⟩
    cases p <;> rfl
  rw [hp,rotatedMidpoint_step]

/-- Equality of geometric midpoints identifies both the original lifted vertex
and its oriented port. The reverse-oriented edge is excluded by the arrow field. -/
lemma loopMidpointPosition_eq_implies_lift_port_eq (a b : ℕ)
    (he : loopMidpointPosition ω s h d a = loopMidpointPosition ω s h d b) :
    loopLiftPosition ω s h d a = loopLiftPosition ω s h d b ∧
      ((directedStep ω s h)^[a] d).val.2 = ((directedStep ω s h)^[b] d).val.2 := by
  rcases (rotatedMidpoint_eq_iff _ _ _ _).mp he with hh | ⟨hz,hp⟩
  · exact hh
  · let e := (directedStep ω s h)^[a] d
    let f := (directedStep ω s h)^[b] d
    have hpz := loopLiftPosition_projection ω s h d a
    have hpf := loopLiftPosition_projection ω s h d b
    have hstep := loopLiftPosition_step_projection (Fin.pos d.val.1.1) (Fin.pos d.val.1.2)
      s e.val (loopLiftPosition ω s h d a) (congrArg Prod.fst hpz) (congrArg Prod.snd hpz)
    have hvertex : f.val.1 = (edgeReverse e.val).1 := by
      rw [← hpf, hz, ← increment_pair]
      exact hstep
    have heq : f.val = edgeReverse e.val := by
      apply Prod.ext hvertex
      change f.val.2 = oppositePort e.val.2 at hp
      rw [hp]
      rcases e with ⟨⟨v,p⟩,he⟩
      cases p <;> rfl
    have hout := f.property
    rw [heq,dartOut_edgeReverse,e.property] at hout
    cases hout

/-- No two times before the least period have the same geometric midpoint.
The opposite orientation of an indexed edge is excluded by the arrow field. -/
theorem loopMidpointPosition_injective :
    Function.Injective (fun k : Fin (loopPeriod ω s h d) => loopMidpointPosition ω s h d k.val) := by
  intro k l he
  obtain ⟨hz, hp⟩ := loopMidpointPosition_eq_implies_lift_port_eq ω s h d k l he
  exact loopLiftPosition_port_injective ω s h d (Prod.ext hz hp)

/-- Zero winding closes the geometric midpoint polygon after one least period. -/
theorem loopMidpointPosition_closed_of_zero_winding (i : Fin N) (j : Fin M)
    (hv : loopVertical ω s h j (directedLoopOf ω s h d) = 0)
    (hh : loopSum ω s h (horizontalCross i) (directedLoopOf ω s h d) = 0) :
    loopMidpointPosition ω s h d (loopPeriod ω s h d) = loopMidpointPosition ω s h d 0 := by
  have hz := (loopLiftPosition_period_eq_start_iff ω s h d i j).mpr ⟨hv,hh⟩
  have hp := Function.iterate_minimalPeriod (f := directedStep ω s h) (x := d)
  change (directedStep ω s h)^[loopPeriod ω s h d] d = d at hp
  simp [loopMidpointPosition, hz, hp]

end

end PottsDiscontinuity.TorusTopology
