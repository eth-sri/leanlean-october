module

public import proofs.HordijkSteelThreshold.BoundedFoodWords
public import proofs.HordijkSteelThreshold.FiniteBondSeparation

@[expose] public section

namespace HordijkSteelThreshold

open Classical

variable (L N : ℕ)

abbrev WordBasicEdge  := BoundedFoodWord L N × Bool

noncomputable def wordBasicEdges  : Finset (WordBasicEdge L N) :=
  Finset.univ.filter $ fun e => e.1 ≠ boundedFoodRoot L N

def wordEdgeParent {L N : ℕ} (e : WordBasicEdge L N) : BoundedFoodWord L N :=
  if e.2 then boundedFoodRight e.1 else boundedFoodLeft e.1

theorem wordGraph_reaches_root  (v : BoundedFoodWord L N) :
    indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent v (boundedFoodRoot L N) := by
  induction hk : foodWordHeight L v.val using Nat.strong_induction_on generalizing v with
  | _ k ih =>
  by_cases hr : v = boundedFoodRoot L N
  · exact hr ▸ .refl _
  have := foodWordRight_height L v.val
  have := boundedFood_zero_height v
  exact .trans _ _ _ (.rel _ _ ⟨(v, true), by simp [wordBasicEdges, hr], rfl, rfl⟩)
    (ih _ (by change foodWordHeight L (foodWordRight L v.val) < k; grind) (boundedFoodRight v) rfl)

theorem wordGraph_connected  (u v : BoundedFoodWord L N) :
    indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent u v :=
  (wordGraph_reaches_root L N u).trans _ _ _ (wordGraph_reaches_root L N v).symm


noncomputable def wordGraphCut {L N : ℕ} (f : BoundedFoodWord L N → Bool) :
    Finset (WordBasicEdge L N) := booleanEdgeCut (wordBasicEdges L N) Prod.fst wordEdgeParent f

end HordijkSteelThreshold
