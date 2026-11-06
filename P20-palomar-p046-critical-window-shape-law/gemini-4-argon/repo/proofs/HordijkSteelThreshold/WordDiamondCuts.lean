module

public import proofs.HordijkSteelThreshold.WordGraphCuts
public import proofs.HordijkSteelThreshold.LocalParityTransfer

@[expose] public section

namespace HordijkSteelThreshold
open Classical

def wordDiamondSlot {L N : ℕ} (v : BoundedFoodWord L N) : Fin 4 → WordBasicEdge L N :=
  ![(v, false), (v, true), (boundedFoodRight v, false), (boundedFoodLeft v, true)]

noncomputable def wordEdgeIndicator {L N : ℕ} (F : Finset (WordBasicEdge L N))
    (e : WordBasicEdge L N) : Bool := decide (e ∈ F)

theorem wordCut_indicator {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) :
    wordEdgeIndicator (wordGraphCut f) e = (f e.1 ^^ f (wordEdgeParent e)) := by
  by_cases hr : e.1 = boundedFoodRoot L N
  · have hp : wordEdgeParent e = e.1 := by
      unfold wordEdgeParent; rw [hr]; split <;> apply Subtype.ext <;>
        simp [boundedFoodLeft, boundedFoodRight, boundedFoodRoot, foodWordLeft, foodWordRight]
    simp [wordEdgeIndicator, wordGraphCut, booleanEdgeCut, wordBasicEdges, hr, hp]
  · cases ha : f e.1 <;> cases hb : f (wordEdgeParent e) <;>
      simp [wordEdgeIndicator, wordGraphCut, booleanEdgeCut, wordBasicEdges, hr, ha, hb]

theorem wordDiamond_closed_subset_cut {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (F : Finset (WordBasicEdge L N)) (hsub : F ⊆ wordGraphCut f)
    (hclosed : ∀ v i j, wordDiamondSlot v i ∈ F →
      wordDiamondSlot v j ∈ wordGraphCut f → wordDiamondSlot v j ∈ F) :
    ∃ g : BoundedFoodWord L N → Bool, wordGraphCut g = F := by
  let le v := wordEdgeIndicator F (v, false)
  let re v := wordEdgeIndicator F (v, true)
  have hsub' : F ⊆ wordBasicEdges L N := hsub.trans (Finset.filter_subset _ _)
  have hr : le (boundedFoodRoot L N) = false ∧ re (boundedFoodRoot L N) = false := by
    have hn (b : Bool) : (boundedFoodRoot L N, b) ∉ F := fun h => by simpa [wordBasicEdges] using hsub' h
    simp [le, re, wordEdgeIndicator, hn]
  have hpar (v : BoundedFoodWord L N) : quadParity (fun i => wordEdgeIndicator F (wordDiamondSlot v i)) = false := by
    refine quadParity_closed_subset _ (fun i => wordEdgeIndicator (wordGraphCut f) (wordDiamondSlot v i))
      (fun _ hi => decide_eq_true (hsub (of_decide_eq_true hi)))
      (fun i j hi hj => decide_eq_true (hclosed v i j (of_decide_eq_true hi) (of_decide_eq_true hj))) ?_
    simp only [quadParity, wordCut_indicator, wordDiamondSlot, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, wordEdgeParent, Bool.false_eq_true, ite_false, ite_true]
    rw [boundedFoodParents_commute]
    cases f v <;> cases f (boundedFoodLeft v) <;> cases f (boundedFoodRight v) <;>
      cases f (boundedFoodRight (boundedFoodLeft v)) <;> rfl
  refine ⟨diamondPotential boundedFoodRight re N, Finset.ext fun ⟨v, b⟩ => ?_⟩
  have hp := boundedFood_diamond_cut L N le re hr hpar v
  cases b
  · exact decide_eq_decide.mp ((wordCut_indicator _ (v, false)).trans hp.1)
  · exact decide_eq_decide.mp ((wordCut_indicator _ (v, true)).trans hp.2)

end HordijkSteelThreshold
