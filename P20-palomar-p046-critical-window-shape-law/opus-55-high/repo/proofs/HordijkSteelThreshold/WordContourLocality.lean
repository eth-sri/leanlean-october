module

public import proofs.HordijkSteelThreshold.WordContourCounting

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- End insertion/deletion on uncontracted words, including the empty word. -/
def endWordGraph : SimpleGraph (List Bool) where
  Adj u v := ∃ b : Bool, v = b :: u ∨ u = b :: v ∨
    v = u ++ [b] ∨ u = v ++ [b]
  symm := ⟨fun u v ⟨b, h⟩ => ⟨b, by tauto⟩⟩
  loopless := ⟨by
    rintro u ⟨b, h | h | h | h⟩ <;>
      have hh := congrArg List.length h <;> simp at hh⟩

variable {L N : ℕ}

/-- A slot belonging to an actual edge is at most one end edit from its diamond product.
The actual-edge premise prevents a contracted-root jump. -/
theorem wordDiamondSlot_product_walk  (v : BoundedFoodWord L N) (i : Fin 4)
    (he : wordDiamondSlot v i ∈ wordBasicEdges L N) :
    ∃ p : endWordGraph.Walk (wordDiamondSlot v i).1.val v.val, p.length ≤ 1 := by
  fin_cases i
  · tauto
  · tauto
  · obtain ⟨b, hb⟩ := boundedFoodRight_preimage v _ (by simpa [wordBasicEdges, wordDiamondSlot] using he) rfl
    exact ⟨.cons ⟨b, by tauto⟩ .nil, le_rfl⟩
  · obtain ⟨b, hb⟩ := boundedFoodLeft_preimage v _ (by simpa [wordBasicEdges, wordDiamondSlot] using he) rfl
    exact ⟨.cons ⟨b, by tauto⟩ .nil, le_rfl⟩

theorem wordDiamond_products_walk  (e d : WordBasicEdge L N)
    (he : e ∈ wordBasicEdges L N) (hd : d ∈ wordBasicEdges L N)
    (ha : wordDiamondAdjacent e d) :
    ∃ p : endWordGraph.Walk e.1.val d.1.val, p.length ≤ 2 := by
  obtain ⟨v, i, j, rfl, rfl⟩ := ha
  obtain ⟨p, hp⟩ := wordDiamondSlot_product_walk v i he
  obtain ⟨q, hq⟩ := wordDiamondSlot_product_walk v j hd
  exact ⟨p.append q.reverse, by simp; omega⟩

/-- Lift a contour walk to literal end edits, paying at most two per diamond step. -/
theorem wordContour_walk_lift  {e d : WordBasicEdge L N}
    (p : (wordContourGraph L N).Walk e d) :
    ∃ q : endWordGraph.Walk e.1.val d.1.val, q.length ≤ 2 * p.length := by
  induction p with
  | nil => simp_all
  | @cons u v w huv p ih =>
    obtain ⟨q, hq⟩ := wordDiamond_products_walk u v huv.1 huv.2.1 huv.2.2.2
    obtain ⟨s, hs⟩ := ih
    exact ⟨q.append s, by simp; omega⟩

/-- Every boundary product is within 4(b-1) end edits of any chosen boundary product.
This is contour localization, not yet molecule-to-contour anchoring. -/
theorem wordContour_product_locality  (C : Finset $ WordBasicEdge L N)
    (hsub : C ⊆ wordBasicEdges L N) (e : WordBasicEdge L N) (he : e ∈ C)
    (hconn : ∀ d ∈ C, wordContourReach C e d)
    (d : WordBasicEdge L N) (hd : d ∈ C) :
    ∃ q : endWordGraph.Walk e.1.val d.1.val, q.length ≤ 4 * (C.card - 1) := by
  obtain ⟨p, hp, hl⟩ := finite_connected_covering_tour (wordContourGraph L N) C e he
    (wordContour_crossing C hsub e hconn)
  have hdp : d ∈ p.support := by aesop
  obtain ⟨q, hq⟩ := wordContour_walk_lift $ p.takeUntil d hdp
  exact ⟨q, by have := p.length_takeUntil_le_length hdp; omega⟩

end HordijkSteelThreshold
