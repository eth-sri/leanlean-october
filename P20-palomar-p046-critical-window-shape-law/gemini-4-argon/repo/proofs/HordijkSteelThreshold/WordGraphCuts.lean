module

public import proofs.HordijkSteelThreshold.BoundedFoodWords
public import proofs.HordijkSteelThreshold.FiniteBondSeparation

@[expose] public section

namespace HordijkSteelThreshold

open Classical

abbrev WordBasicEdge (L N : ℕ) := BoundedFoodWord L N × Bool

noncomputable def wordBasicEdges (L N : ℕ) : Finset (WordBasicEdge L N) :=
  Finset.univ.filter (fun e => e.1 ≠ boundedFoodRoot L N)

def wordEdgeParent {L N : ℕ} (e : WordBasicEdge L N) : BoundedFoodWord L N :=
  if e.2 then boundedFoodRight e.1 else boundedFoodLeft e.1

noncomputable def wordGraphCut {L N : ℕ} (f : BoundedFoodWord L N → Bool) :
    Finset (WordBasicEdge L N) := booleanEdgeCut (wordBasicEdges L N) Prod.fst wordEdgeParent f

theorem wordGraph_disabled_bond (L N : ℕ) (active : Finset (WordBasicEdge L N))
    (u v : BoundedFoodWord L N)
    (h : ¬ indexedEdgeReach active Prod.fst wordEdgeParent u v) :
    ∃ f : BoundedFoodWord L N → Bool, f u ≠ f v ∧
      wordGraphCut f ⊆ wordBasicEdges L N \ active ∧ (wordGraphCut f).Nonempty ∧
      ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
        wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f := by
  have hroot (k : ℕ) : ∀ w : BoundedFoodWord L N, foodWordHeight L w.val ≤ k →
      indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent w (boundedFoodRoot L N) := by
    induction k with
    | zero => intro w hw; rw [boundedFood_zero_height w (by omega)]; exact .refl _
    | succ k ih =>
      intro w hw
      by_cases hr : w = boundedFoodRoot L N
      · exact hr ▸ .refl _
      · have := foodWordRight_height L w.val
        exact .trans _ _ _ (.rel _ _ ⟨(w, true), by simp [wordBasicEdges, hr], rfl, rfl⟩)
          (ih (boundedFoodRight w) (by change foodWordHeight L (foodWordRight L w.val) ≤ k; omega))
  exact exists_disabled_separating_bond (wordBasicEdges L N) active Prod.fst wordEdgeParent u v
    (.trans _ _ _ (hroot N u (by have := boundedFoodWord_length_le u; unfold foodWordHeight; omega))
      (.symm _ _ (hroot N v (by have := boundedFoodWord_length_le v; unfold foodWordHeight; omega)))) h

end HordijkSteelThreshold
