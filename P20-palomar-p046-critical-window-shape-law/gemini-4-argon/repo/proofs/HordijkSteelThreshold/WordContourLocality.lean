module

public import proofs.HordijkSteelThreshold.WordContourCounting

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- End insertion/deletion on uncontracted words, including the empty word. -/
def endWordGraph : SimpleGraph (List Bool) where
  Adj u v := ∃ b : Bool, v = b :: u ∨ u = b :: v ∨
    v = u ++ [b] ∨ u = v ++ [b]
  symm := ⟨by
    rintro u v ⟨b, h | h | h | h⟩
    · exact ⟨b, Or.inr (Or.inl h)⟩
    · exact ⟨b, Or.inl h⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inr h))⟩
    · exact ⟨b, Or.inr (Or.inr (Or.inl h))⟩⟩
  loopless := ⟨by
    rintro u ⟨b, h | h | h | h⟩ <;>
      have hh := congrArg List.length h <;> simp at hh⟩

theorem wordDiamondSlot_product_walk {L N : ℕ} (v : BoundedFoodWord L N) (i : Fin 4)
    (he : wordDiamondSlot v i ∈ wordBasicEdges L N) :
    ∃ p : endWordGraph.Walk (wordDiamondSlot v i).1.val v.val, p.length ≤ 1 := by
  fin_cases i
  · exact ⟨Walk.nil, Nat.zero_le 1⟩
  · exact ⟨Walk.nil, Nat.zero_le 1⟩
  · obtain ⟨b, hb⟩ := boundedFoodRight_preimage v _ (by simpa [wordBasicEdges, wordDiamondSlot] using he) rfl
    exact ⟨Walk.cons ⟨b, Or.inr (Or.inr (Or.inl hb))⟩ Walk.nil, le_rfl⟩
  · obtain ⟨b, hb⟩ := boundedFoodLeft_preimage v _ (by simpa [wordBasicEdges, wordDiamondSlot] using he) rfl
    exact ⟨Walk.cons ⟨b, Or.inl hb⟩ Walk.nil, le_rfl⟩

theorem wordContour_product_locality {L N : ℕ} (C : Finset (WordBasicEdge L N))
    (hsub : C ⊆ wordBasicEdges L N) (e : WordBasicEdge L N) (he : e ∈ C)
    (hconn : ∀ d ∈ C, wordContourReach C e d)
    (d : WordBasicEdge L N) (hd : d ∈ C) :
    ∃ q : endWordGraph.Walk e.1.val d.1.val, q.length ≤ 4 * (C.card - 1) := by
  have hlift {u v : WordBasicEdge L N} (p : (wordContourGraph L N).Walk u v) :
      ∃ q : endWordGraph.Walk u.1.val v.1.val, q.length ≤ 2 * p.length := by
    induction p with
    | nil => exact ⟨Walk.nil, by simp⟩
    | @cons a b c hab p ih =>
      obtain ⟨w, i, j, rfl, rfl⟩ := hab.2.2.2
      obtain ⟨p₁, hp₁⟩ := wordDiamondSlot_product_walk w i hab.1
      obtain ⟨p₂, hp₂⟩ := wordDiamondSlot_product_walk w j hab.2.1
      obtain ⟨s, hs⟩ := ih
      exact ⟨(p₁.append p₂.reverse).append s, by simp; omega⟩
  obtain ⟨p, hp, hl⟩ := finite_connected_covering_tour (wordContourGraph L N) C e he
    (wordContour_crossing C hsub e hconn)
  have hdp : d ∈ p.support := List.mem_toFinset.mp (hp ▸ hd)
  obtain ⟨q, hq⟩ := hlift (p.takeUntil d hdp)
  have ht := p.length_takeUntil_le_length hdp
  exact ⟨q, by omega⟩

end HordijkSteelThreshold
