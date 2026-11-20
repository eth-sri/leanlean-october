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

variable {u v : List J} {dependent : J → J → Prop}
    (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent) {E : Type*} (word : List J)

/-- Actual word occurrences and their mark coordinates. -/
def wordHeapPiecePositionEquiv (dependent : J → J → Prop) :
    WordHeapPiece word dependent ≃ Fin word.length where
  toFun := WordHeapPiece.position
  invFun i := ⟨i⟩
  left_inv x := by rfl
  right_inv _ := rfl

/-- A true heap isomorphism induces a bijection of actual mark coordinates. -/
def historyHeapCoordinateEquiv : Fin u.length ≃ Fin v.length :=
  (wordHeapPiecePositionEquiv u dependent).symm.trans
    (e.toEquiv.trans (wordHeapPiecePositionEquiv v dependent))

@[simp] theorem historyHeapCoordinateEquiv_position (x : WordHeapPiece u dependent) :
    historyHeapCoordinateEquiv e x.position = (e x).position := rfl

/-- This is the actual measurable coordinate insertion into another word representative. -/
def historyHeapMarkEquiv [MeasurableSpace E] :
    (Fin u.length → E) ≃ᵐ (Fin v.length → E) :=
  MeasurableEquiv.piCongrLeft (fun _ => E) (historyHeapCoordinateEquiv e)

@[simp] theorem historyHeapMarkEquiv_position [MeasurableSpace E]
    (marks : Fin u.length → E) (x : WordHeapPiece u dependent) :
    historyHeapMarkEquiv e marks (e x).position = marks x.position := by
  simpa only [historyHeapMarkEquiv, historyHeapCoordinateEquiv_position] using MeasurableEquiv.piCongrLeft_apply_apply (historyHeapCoordinateEquiv e) (β := fun _ => E) marks x.position

end NearlyMinimax
