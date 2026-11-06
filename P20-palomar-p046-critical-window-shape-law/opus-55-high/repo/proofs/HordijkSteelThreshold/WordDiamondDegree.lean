module

public import proofs.HordijkSteelThreshold.WordParentFibers
public import proofs.HordijkSteelThreshold.WordBondConnected

@[expose] public section

namespace HordijkSteelThreshold
open Classical

variable {L N : ℕ}

variable (e : WordBasicEdge L N)

noncomputable def wordDiamondIncidence   :=
  Finset.univ.filter (fun v : BoundedFoodWord L N => ∃ i, wordDiamondSlot v i = e)

theorem wordDiamond_incidence_card
    (he : e ∈ wordBasicEdges L N) : (wordDiamondIncidence e).card ≤ 3 := by
  rcases e with ⟨u, b⟩
  have hn : u ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using he
  have := boundedFoodRight_fiber_card u hn
  have := boundedFoodLeft_fiber_card u hn
  refine (Finset.card_le_card (t := insert u $ Finset.univ.filter fun v =>
    (if b then boundedFoodLeft v else boundedFoodRight v) = u) fun v hv => ?_).trans
    ((Finset.card_insert_le _ _).trans ?_)
  · obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hv).2
    fin_cases i <;> cases b <;> simp_all [wordDiamondSlot]
  · cases b <;> simp <;> omega

noncomputable def wordDiamondEdges  (v : BoundedFoodWord L N) :=
  (Finset.univ : Finset $ Fin 4).image $ wordDiamondSlot v

noncomputable def wordDiamondNeighbors   :=
  (wordDiamondIncidence e).biUnion $ fun v => (wordDiamondEdges v).erase e

theorem wordDiamond_neighbors_card
    (he : e ∈ wordBasicEdges L N) : (wordDiamondNeighbors e).card ≤ 9 := by
  refine Finset.card_biUnion_le.trans $ (Finset.sum_le_card_nsmul _ _ 3 fun v hv => ?_).trans
    (by have := wordDiamond_incidence_card e he; simp; omega)
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hv).2
  have hm : e ∈ wordDiamondEdges v := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  have hc : (wordDiamondEdges v).card ≤ 4 := Finset.card_image_le.trans $ by decide
  simp_all


theorem wordDiamond_neighbor_iff  (e d : WordBasicEdge L N) :
    d ∈ wordDiamondNeighbors e ↔ d ≠ e ∧ wordDiamondAdjacent e d := by
  simp only [wordDiamondNeighbors, Finset.mem_biUnion, Finset.mem_erase,
    wordDiamondIncidence, Finset.mem_filter, Finset.mem_univ, true_and,
    wordDiamondEdges, Finset.mem_image]
  exact ⟨fun ⟨v, ⟨i, hi⟩, hd, j, hj⟩ => ⟨hd, v, i, j, hi, hj⟩,
    fun ⟨hd, v, i, j, hi, hj⟩ => ⟨v, ⟨i, hi⟩, hd, j, hj⟩⟩

end HordijkSteelThreshold
