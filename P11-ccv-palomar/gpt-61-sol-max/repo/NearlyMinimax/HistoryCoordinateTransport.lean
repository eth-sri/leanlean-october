module

public import NearlyMinimax.HistoryWordTransport
public import NearlyMinimax.HistoryPriorMeasureIdentity

@[expose] public section

/-!
# True finite mark-law and density transport through heap coordinates
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax

variable {J : Type*}

/-- Actual word occurrences and their mark coordinates. -/
def wordHeapPiecePositionEquiv (word : List J) (dependent : J → J → Prop) :
    WordHeapPiece word dependent ≃ Fin word.length where
  toFun := WordHeapPiece.position
  invFun i := ⟨i⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

section
variable {u v : List J}

section
variable {dependent : J → J → Prop} (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent)
include e

/-- A true heap isomorphism induces a bijection of actual mark coordinates. -/
def historyHeapCoordinateEquiv    :=
  (wordHeapPiecePositionEquiv u dependent).symm.trans
    (e.toEquiv.trans (wordHeapPiecePositionEquiv v dependent))

@[simp] theorem historyHeapCoordinateEquiv_position   x :
    historyHeapCoordinateEquiv e x.position = (e x).position := by
  cases x
  rfl
end


/-- This is the actual measurable coordinate insertion into another word representative. -/
def historyHeapMarkEquiv  {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} [MeasurableSpace E] :
    (Fin u.length → E) ≃ᵐ (Fin v.length → E) :=
  MeasurableEquiv.piCongrLeft (fun _ => E) (historyHeapCoordinateEquiv e)

@[simp] theorem historyHeapMarkEquiv_position  {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} [MeasurableSpace E]
    (marks : Fin u.length → E) (x : WordHeapPiece u dependent) :
    historyHeapMarkEquiv e marks (e x).position = marks x.position := by
  have hh := MeasurableEquiv.piCongrLeft_apply_apply (historyHeapCoordinateEquiv e)
    (β := fun _ : Fin v.length => E) marks x.position
  solve_by_elim []
end


end NearlyMinimax
