module

public import PottsDiscontinuity.RCInfinite.MeasurableBounds

@[expose] public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- Prescribe one edge state, retaining all other original edge states. -/
def setEdge (e : Edge) (b : Bool) (ω : LatticeConfiguration) : LatticeConfiguration :=
  fun f => if f = e then b else ω f

@[simp] theorem setEdge_self (e : Edge) (b : Bool) (ω : LatticeConfiguration) :
    setEdge e b ω e = b := by simp [setEdge]

@[simp] theorem setEdge_setEdge (e : Edge) (b c : Bool) (ω : LatticeConfiguration) :
    setEdge e b (setEdge e c ω) = setEdge e b ω := by
  funext f
  by_cases hf : f = e <;> simp [setEdge, hf]

/-- Prescribe exactly the states in a finite edge set. -/
def setEdges (F : Finset Edge) (ξ : Edge → Bool) (ω : LatticeConfiguration) : LatticeConfiguration :=
  fun e => if e ∈ F then ξ e else ω e

@[simp] theorem setEdges_empty (ξ : Edge → Bool) : setEdges ∅ ξ = id := by
  funext ω e
  simp [setEdges]

end
end PottsDiscontinuity.RCInfinite
