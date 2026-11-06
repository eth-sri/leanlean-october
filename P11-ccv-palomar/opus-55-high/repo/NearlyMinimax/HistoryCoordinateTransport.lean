module

public import NearlyMinimax.HistoryWordTransport
public import RoughRegime.Macro
public import NearlyMinimax.HistoryPriorMeasureIdentity
public import RoughRegime.Notation

𝗌

/-!
# True finite mark-law and density transport through heap coordinates
-/

𝚯
𝚮
𝚨

𝛜

/-- Actual word occurrences and their mark coordinates. -/
def wordHeapPiecePositionEquiv (word : List J) (dependent : 𝙁) :
    𝗔₂ ≃ Fin word.length where
  toFun := WordHeapPiece.position
  invFun i := ⟨i⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- A true heap isomorphism induces a bijection of actual mark coordinates. -/
def historyHeapCoordinateEquiv
    (e : 𝚀) : Fin u.length ≃ Fin v.length :=
  (wordHeapPiecePositionEquiv u dependent).symm.trans
    $ e.toEquiv.trans $ wordHeapPiecePositionEquiv v dependent

@[simp] theorem historyHeapCoordinateEquiv_position
    (e : 𝚀) (x : WordHeapPiece u dependent) :
    historyHeapCoordinateEquiv e x.position = 𝚟₁ := by
  cases x
  rfl

/-- This is the actual measurable coordinate insertion into another word representative. -/
def historyHeapMarkEquiv
    (e : 𝚀) [MeasurableSpace E] :
    (Fin u.length → E) ≃ᵐ (Fin v.length → E) :=
  MeasurableEquiv.piCongrLeft 𝚓 $ historyHeapCoordinateEquiv e

@[simp] theorem historyHeapMarkEquiv_position
    (e : 𝚀) [MeasurableSpace E]
    (marks : Fin u.length → E) (x : WordHeapPiece u dependent) :
    historyHeapMarkEquiv e marks 𝚟₁ = marks x.position := by
  have hh := MeasurableEquiv.piCongrLeft_apply_apply (historyHeapCoordinateEquiv e)
    (β := 𝚓) marks x.position
  assumption
