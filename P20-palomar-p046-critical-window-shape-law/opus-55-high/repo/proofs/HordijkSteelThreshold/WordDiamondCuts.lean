module

public import proofs.HordijkSteelThreshold.WordGraphCuts
public import proofs.HordijkSteelThreshold.LocalParityTransfer

@[expose] public section

namespace HordijkSteelThreshold
open Classical

variable {L N : ℕ}

def wordDiamondSlot  (v : BoundedFoodWord L N) : Fin 4 → WordBasicEdge L N :=
  ![(v, false), (v, true), (boundedFoodRight v, false), (boundedFoodLeft v, true)]

noncomputable def wordEdgeIndicator  (F : Finset $ WordBasicEdge L N)
    (e : WordBasicEdge L N) : Bool := decide $ e ∈ F

variable (f : BoundedFoodWord L N → Bool)

theorem wordCut_indicator
    (e : WordBasicEdge L N) :
    wordEdgeIndicator (wordGraphCut f) e = (f e.1 ^^ f (wordEdgeParent e)) := by
  by_cases hr : e.1 = boundedFoodRoot L N
  · have hp : wordEdgeParent e = e.1 := by unfold wordEdgeParent; aesop
    simp [wordEdgeIndicator, wordGraphCut, booleanEdgeCut, hp]
  · cases ha : f e.1 <;> cases hb : f (wordEdgeParent e) <;>
      simp [wordEdgeIndicator, wordGraphCut, booleanEdgeCut, wordBasicEdges, hr, ha, hb]

theorem wordCut_diamond_parity
    (v : BoundedFoodWord L N) :
    quadParity (wordEdgeIndicator (wordGraphCut f) $ wordDiamondSlot v ·) = false := by
  simp only [quadParity, wordCut_indicator, wordDiamondSlot, Matrix.cons_val, wordEdgeParent,
    Bool.false_eq_true, ite_false, ite_true]
  rw [boundedFoodParents_commute]
  cases f v <;> cases f (boundedFoodLeft v) <;> cases f (boundedFoodRight v) <;>
    cases f (boundedFoodRight $ boundedFoodLeft v) <;> rfl

end HordijkSteelThreshold
