module

public import proofs.HordijkSteelThreshold.DisjointDetourSelection
public import proofs.HordijkSteelThreshold.WordDetourSource

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def wordContourDetours {L N : ℕ} (w : ℕ)
    (C : Finset $ WordBasicEdge L N) : Finset (WordShortKey L N w) :=
  C.product Finset.univ

variable {L N w : ℕ}

@[simp] theorem wordContourDetours_card  (C : Finset $ WordBasicEdge L N) :
    (wordContourDetours w C).card = w*C.card := by
  simp [wordContourDetours, Nat.mul_comm]

theorem wordContour_disjoint_detours  (hL : 2*w ≤ L)
    (C : Finset $ WordBasicEdge L N) :
    ∃ T ⊆ wordContourDetours w C,
      (∀ d ∈ T, ∀ e ∈ T, d ≠ e →
        Disjoint (wordDetourSourceReactions hL d) (wordDetourSourceReactions hL e)) ∧
      w*C.card ≤ 5*T.card := by
  have huse r := (Finset.card_le_card $ Finset.filter_subset_filter _ $ Finset.subset_univ $ wordContourDetours w C).trans
    (wordDetourSourceReactions_incidence hL r)
  have hsize := wordDetourSourceReactions_card (N := N) hL
  rw [← wordContourDetours_card]
  generalize wordContourDetours w C = S at *
  generalize wordDetourSourceReactions hL = support at *
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image (S.powerset.filter fun T =>
    ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (support i) (support j)) Finset.card ⟨∅, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hT hmax
  refine ⟨T, hT.1, hT.2, (Finset.card_le_card (t := T.biUnion fun j => insert j $ (support j).biUnion
    fun r => (S.filter (r ∈ support ·)).erase j) fun i hi => ?_).trans $ Finset.card_biUnion_le.trans
    ((Finset.sum_le_card_nsmul _ _ 5 fun j hj => (Finset.card_insert_le _ _).trans ?_).trans $ by simp [Nat.mul_comm])⟩
  · by_cases hiT : i ∈ T
    · grind
    by_cases hex : ∃ j ∈ T, ¬ Disjoint (support i) (support j)
    · simp [Finset.not_disjoint_iff] at hex ⊢
      grind
    · have := hmax (insert i T) ⟨Finset.insert_subset hi hT.1, by grind⟩
      rw [Finset.card_insert_of_notMem hiT] at this
      omega
  · have h := Finset.card_biUnion_le.trans (Finset.sum_le_card_nsmul (support j) (fun r => ((S.filter (r ∈ support ·)).erase j).card) 2 fun r hr => by
      have := Finset.card_erase_add_one (s := S.filter (r ∈ support ·)) (a := j) (by simp [hT.1 hj, hr]); have := huse r; omega)
    have := hsize j
    simp_all
    omega


end HordijkSteelThreshold
