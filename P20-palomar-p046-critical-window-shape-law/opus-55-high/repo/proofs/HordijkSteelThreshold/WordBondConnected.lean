module

public import proofs.HordijkSteelThreshold.WordDiamondCuts

@[expose] public section

namespace HordijkSteelThreshold
open Classical

variable {L N : ℕ}

/-- Two indexed edges share a finite diamond; loops are harmless for reachability. -/
def wordDiamondAdjacent  (e d : WordBasicEdge L N) : Prop :=
  ∃ v i j, wordDiamondSlot v i = e ∧ wordDiamondSlot v j = d

def wordContourReach  (C : Finset $ WordBasicEdge L N) :=
  Relation.EqvGen $ fun e d => e ∈ C ∧ d ∈ C ∧ wordDiamondAdjacent e d

/-- A nonempty cut minimal among nonempty cuts is connected through diamonds.
This is the contour theorem used before counting connected edge sets. -/
theorem wordBond_diamond_connected  (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (e d : WordBasicEdge L N) (he : e ∈ wordGraphCut f) (hd : d ∈ wordGraphCut f) :
    wordContourReach (wordGraphCut f) e d := by
  let F := (wordGraphCut f).filter $ wordContourReach (wordGraphCut f) e
  have heF : e ∈ F := Finset.mem_filter.mpr ⟨he, .refl e⟩
  obtain ⟨g, hg⟩ : ∃ g, wordGraphCut g = F := by
    have hpar v := quadParity_closed_subset (wordEdgeIndicator F $ wordDiamondSlot v ·) _
      (fun _ hi => decide_eq_true $ Finset.filter_subset _ _ $ of_decide_eq_true hi)
      (fun i j hi hj => by
        simp only [wordEdgeIndicator, F, decide_eq_true_eq, Finset.mem_filter] at hi hj ⊢
        exact ⟨hj, .trans _ _ _ hi.2 $ .rel _ _ ⟨hi.1, hj, v, i, j, rfl, rfl⟩⟩)
      (wordCut_diamond_parity f v)
    have hsub : F ⊆ wordBasicEdges L N := (Finset.filter_subset _ _).trans $ Finset.filter_subset _ _
    let le := fun v => wordEdgeIndicator F (v, false)
    let re := fun v => wordEdgeIndicator F (v, true)
    have hn b : (boundedFoodRoot L N, b) ∉ F := fun h => by simpa [wordBasicEdges] using hsub h
    refine ⟨diamondPotential boundedFoodRight re N, ?_⟩
    ext ⟨v, b⟩
    have hp : ∀ k v, foodWordHeight L v.val ≤ k →
        (diamondPotential boundedFoodRight re k v ^^ diamondPotential boundedFoodRight re k (boundedFoodLeft v)) = le v ∧
        (diamondPotential boundedFoodRight re k v ^^ diamondPotential boundedFoodRight re k (boundedFoodRight v)) = re v := by
      intro k
      induction k with
      | zero =>
        intro u hu
        have := boundedFood_zero_height u $ by omega
        subst this
        simp [le, re, wordEdgeIndicator, hn, diamondPotential]
      | succ k ih =>
        intro u hu
        obtain ⟨hil, hir⟩ := ih (boundedFoodRight u) (by have : foodWordHeight L (boundedFoodRight u).val ≤ _ := foodWordRight_height L u.val; omega)
        have : (((le u ^^ re u) ^^ le (boundedFoodRight u)) ^^ re (boundedFoodLeft u)) = false := hpar u
        rw [boundedFoodParents_commute] at hil
        simp only [diamondPotential, ← hir]
        revert this hil hir
        cases le u <;> cases re u <;> cases le (boundedFoodRight u) <;> cases re (boundedFoodLeft u) <;>
          cases diamondPotential boundedFoodRight re k (boundedFoodRight u) <;>
          cases diamondPotential boundedFoodRight re k (boundedFoodRight $ boundedFoodLeft u) <;> simp
    replace hp := hp N v (by have := boundedFoodWord_length_le v; unfold foodWordHeight; omega)
    have hi := wordCut_indicator (diamondPotential boundedFoodRight re N) (v, b)
    cases b <;> simp_all [ re, wordEdgeParent] <;> exact decide_eq_decide.1 hi
  grind

end HordijkSteelThreshold
