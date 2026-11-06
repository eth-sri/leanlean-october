module

public import proofs.HordijkSteelThreshold.WordParentFibers
public import proofs.HordijkSteelThreshold.WordBondConnected

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def wordDiamondIncidence {L N : ℕ} (e : WordBasicEdge L N) :=
  Finset.univ.filter (fun v : BoundedFoodWord L N => ∃ i, wordDiamondSlot v i = e)

noncomputable def wordDiamondEdges {L N : ℕ} (v : BoundedFoodWord L N) :=
  (Finset.univ : Finset (Fin 4)).image (wordDiamondSlot v)

noncomputable def wordDiamondNeighbors {L N : ℕ} (e : WordBasicEdge L N) :=
  (wordDiamondIncidence e).biUnion (fun v => (wordDiamondEdges v).erase e)

theorem wordDiamond_neighbors_card {L N : ℕ} (e : WordBasicEdge L N)
    (he : e ∈ wordBasicEdges L N) : (wordDiamondNeighbors e).card ≤ 9 := by
  have hinc : (wordDiamondIncidence e).card ≤ 3 := by
    have hn : e.1 ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using he
    rcases e with ⟨u, b⟩; cases b
    · exact (Finset.card_le_card (t := insert u (Finset.univ.filter fun v => boundedFoodRight v = u))
        fun v hv => by obtain ⟨_, i, hi⟩ := Finset.mem_filter.mp hv; fin_cases i <;> simp_all [wordDiamondSlot]).trans
        ((Finset.card_insert_le _ _).trans (by have := boundedFoodRight_fiber_card u hn; omega))
    · exact (Finset.card_le_card (t := insert u (Finset.univ.filter fun v => boundedFoodLeft v = u))
        fun v hv => by obtain ⟨_, i, hi⟩ := Finset.mem_filter.mp hv; fin_cases i <;> simp_all [wordDiamondSlot]).trans
        ((Finset.card_insert_le _ _).trans (by have := boundedFoodLeft_fiber_card u hn; omega))
  refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum (g := fun _ => 3) fun v hv => ?_).trans (by simp; omega))
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hv).2
  have hm : e ∈ wordDiamondEdges v := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
  have hc : (wordDiamondEdges v).card ≤ 4 := Finset.card_image_le.trans (by decide)
  rw [Finset.card_erase_of_mem hm]; omega

theorem wordDiamond_neighbor_iff {L N : ℕ} (e d : WordBasicEdge L N) :
    d ∈ wordDiamondNeighbors e ↔ d ≠ e ∧ wordDiamondAdjacent e d := by
  simp only [wordDiamondNeighbors, Finset.mem_biUnion, Finset.mem_erase,
    wordDiamondIncidence, Finset.mem_filter, Finset.mem_univ, true_and,
    wordDiamondEdges, Finset.mem_image]
  exact ⟨fun ⟨v, ⟨i, hi⟩, hd, j, hj⟩ => ⟨hd, v, i, j, hi, hj⟩,
    fun ⟨hd, v, i, j, hi, hj⟩ => ⟨v, ⟨i, hi⟩, hd, j, hj⟩⟩

end HordijkSteelThreshold
