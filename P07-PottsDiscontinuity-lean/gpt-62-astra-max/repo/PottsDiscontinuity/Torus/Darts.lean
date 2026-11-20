module

public import PottsDiscontinuity.Torus.SmoothingSum

/-!
# The finite dart permutation of a smoothed medial torus

A dart is an incident edge slot at a vertex, directed away from that vertex.
Edge reversal and the local smoothing are fixed-point-free involutions. Their
composition follows a smoothed path. Restricting to the darts following a compatible
arrow field gives a finite permutation whose cycles are the oriented loops.

This is a direct combinatorial construction from the definitions above.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

/-- The four incident edge slots, in the coordinate convention of `ArrowConfig`. -/
inductive Port
  | west | east | south | north
  deriving DecidableEq

instance : Fintype Port :=
  ⟨{.west, .east, .south, .north}, by intro p; cases p <;> simp⟩

/-- An incident edge slot at a medial vertex. -/
abbrev Dart (N M : ℕ) := (Fin N × Fin M) × Port

/-- The two turning pairings. Straight-through strands are excluded. -/
def pairedPort : Bool → Port → Port
  | false, .west => .north
  | false, .north => .west
  | false, .east => .south
  | false, .south => .east
  | true, .west => .south
  | true, .south => .west
  | true, .east => .north
  | true, .north => .east

theorem pairedPort_involutive (b : Bool) : Function.Involutive (pairedPort b) := by
  cases b <;> intro p <;> cases p <;> rfl

variable {N M : ℕ}

/-- Reverse a dart along its indexed torus edge. -/
def edgeReverse : Dart N M → Dart N M
  | ((i, j), .west) => ((prv i, j), .east)
  | ((i, j), .east) => ((nxt i, j), .west)
  | ((i, j), .south) => ((i, prv j), .north)
  | ((i, j), .north) => ((i, nxt j), .south)

@[simp] theorem edgeReverse_involutive : Function.Involutive (@edgeReverse N M) := by
  rintro ⟨⟨i, j⟩, p⟩
  cases p <;> simp only [edgeReverse, prv, nxt,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The edge-reversal permutation. -/
def edgePerm (N M : ℕ) : Equiv.Perm (Dart N M) :=
  ⟨edgeReverse, edgeReverse, edgeReverse_involutive, edgeReverse_involutive⟩

section
variable (s : Smoothing N M) (ω : ArrowConfig N M) (d : Dart N M)

include s d in
/-- Reverse direction along the local strand, without crossing a torus edge. -/
def strandReverse : Dart N M :=
  (d.1, pairedPort (s d.1) d.2)

@[simp] theorem strandReverse_involutive :
    Function.Involutive (strandReverse s) := by
  rintro ⟨v, p⟩
  exact Prod.ext rfl (pairedPort_involutive _ p)

include s in
/-- The local strand-reversal permutation. -/
def strandPerm : Equiv.Perm (Dart N M) :=
  ⟨strandReverse s, strandReverse s,
    strandReverse_involutive s, strandReverse_involutive s⟩

include s in
/-- Traverse one torus edge and then turn along the chosen strand at its endpoint. -/
def stepPerm : Equiv.Perm (Dart N M) :=
  (edgePerm N M).trans (strandPerm s)

@[simp] theorem stepPerm_apply :
    stepPerm s d = strandReverse s (edgeReverse d) := rfl

@[simp] theorem stepPerm_symm_apply :
    (stepPerm s).symm d = edgeReverse (strandReverse s d) := rfl

/-- Edge reversal conjugates a path step into its inverse. -/
theorem edgeReverse_step :
    edgeReverse (stepPerm s d) = (stepPerm s).symm (edgeReverse d) := by
  simp

/-- Whether a local edge slot points out of its vertex. -/
def localOut (l r d u : Bool) : Port → Bool
  | .west => !l
  | .east => r
  | .south => !d
  | .north => u

include ω d in
/-- Whether a dart agrees with the arrow carried by its edge. -/
def dartOut : Bool :=
  localOut (ω.left d.1) (ω.right d.1) (ω.below d.1) (ω.above d.1) d.2

@[simp] theorem dartOut_edgeReverse :
    dartOut ω (edgeReverse d) = !dartOut ω d := by
  rcases d with ⟨⟨i, j⟩, p⟩
  cases p <;> simp only [dartOut, localOut, edgeReverse, ArrowConfig.left,
    ArrowConfig.right, ArrowConfig.below, ArrowConfig.above, prv, nxt,
    Equiv.symm_apply_apply, Bool.not_not]

end

theorem localOut_pairedPort (s l r d u : Bool) (h : Compatible s l r d u) (p : Port) :
    localOut l r d u (pairedPort s p) = !localOut l r d u p := by
  revert s l r d u p
  decide

section
variable {ω : ArrowConfig N M} {s : Smoothing N M} (h : CompatibleConfig ω s) (d : Dart N M)

include h in
theorem dartOut_strandReverse :
    dartOut ω (strandReverse s d) = !dartOut ω d :=
  localOut_pairedPort _ _ _ _ _ (h d.1) d.2

include h in
/-- Compatible arrows are preserved when following a full smoothed-path step. -/
theorem dartOut_step :
    dartOut ω (stepPerm s d) = dartOut ω d := by
  simp [dartOut_strandReverse h]

/-- One directed representative of every edge, selected by its arrow. -/
abbrev DirectedDart (ω : ArrowConfig N M) := {d : Dart N M // dartOut ω d = true}

include h in
/-- Following the arrows and smoothing gives a permutation of directed edges. -/
def directedStep : Equiv.Perm (DirectedDart ω) :=
  (stepPerm s).subtypeEquiv (fun d => by rw [dartOut_step h])

@[simp] theorem directedStep_val (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) :
    (directedStep h d).val = stepPerm s d.val := rfl

include h in
/-- Cyclic reindexing of a directed smoothed loop is precisely the same-cycle relation. -/
abbrev DirectedLoop :=
  Quotient (Equiv.Perm.SameCycle.setoid (directedStep h))

end

noncomputable instance (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) : Fintype (DirectedLoop h) :=
  Fintype.ofFinite _

/-- The loop containing a directed edge. Every directed edge has exactly one such class. -/
def directedLoopOf {ω : ArrowConfig N M} {s : Smoothing N M}
    (h : CompatibleConfig ω s) (d : DirectedDart ω) : DirectedLoop h :=
  Quotient.mk _ d

/-- A full path step stays on the same loop. -/
theorem directedLoopOf_step (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) :
    directedLoopOf h (directedStep h d) = directedLoopOf h d := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl _ d).apply_left

end PottsDiscontinuity.Torus
