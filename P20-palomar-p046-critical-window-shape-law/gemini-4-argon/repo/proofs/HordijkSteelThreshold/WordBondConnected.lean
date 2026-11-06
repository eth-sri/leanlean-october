module

public import proofs.HordijkSteelThreshold.WordDiamondCuts

@[expose] public section

namespace HordijkSteelThreshold
open Classical

/-- Two indexed edges share a finite diamond; loops are harmless for reachability. -/
def wordDiamondAdjacent {L N : ℕ} (e d : WordBasicEdge L N) : Prop :=
  ∃ v i j, wordDiamondSlot v i = e ∧ wordDiamondSlot v j = d

def wordContourReach {L N : ℕ} (C : Finset (WordBasicEdge L N)) :=
  Relation.EqvGen (fun e d => e ∈ C ∧ d ∈ C ∧ wordDiamondAdjacent e d)

theorem wordBond_diamond_connected {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (e d : WordBasicEdge L N) (he : e ∈ wordGraphCut f) (hd : d ∈ wordGraphCut f) :
    wordContourReach (wordGraphCut f) e d := by
  let F := (wordGraphCut f).filter (fun a => wordContourReach (wordGraphCut f) e a)
  obtain ⟨g, hg⟩ := wordDiamond_closed_subset_cut f F (Finset.filter_subset _ _) fun v i j hi hj =>
    let ⟨hiC, hiR⟩ := Finset.mem_filter.mp hi
    Finset.mem_filter.mpr ⟨hj, .trans _ _ _ hiR (.rel _ _ ⟨hiC, hj, v, i, j, rfl, rfl⟩)⟩
  have hEq : F = wordGraphCut f := hg ▸ hmin g (hg.symm ▸ ⟨e, Finset.mem_filter.mpr ⟨he, .refl e⟩⟩)
    (hg.symm ▸ Finset.filter_subset _ _)
  exact (Finset.mem_filter.mp (hEq.symm ▸ hd)).2

end HordijkSteelThreshold
