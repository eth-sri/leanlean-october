module

public import proofs.HordijkSteelThreshold.WordEndPaths
public import proofs.HordijkSteelThreshold.WordCoreSideVolume

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

theorem wordLongAnchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f)
    (hconn : ∀ d ∈ wordGraphCut f, wordContourReach (wordGraphCut f) e d)
    (hlong : 8 * (wordGraphCut f).card < e.1.val.length) :
    (∀ v : BoundedFoodWord L N, f v ≠ f (boundedFoodRoot L N) →
      ∃ p : endWordGraph.Walk v.val e.1.val, p.length ≤ 64 * (wordGraphCut f).card) ∧
    (((2 ^ (N + 1) - 2) - (wordNonfoodSide f).card ≤ (wordNonfoodSide f).card) →
      ∀ s : List Bool, s.length ≤ N →
        ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card) := by
  let r := 4 * (wordGraphCut f).card
  let core := (e.1.val.drop r).take (e.1.val.length - 2 * r)
  let left := e.1.val.take r
  let right := (e.1.val.drop r).drop (e.1.val.length - 2 * r)
  have hne : core ≠ [] := by rw [← List.length_pos_iff]; simp [core, r]; omega
  have ha : e.1.val = left ++ core ++ right := by simp [left, core, right, List.append_assoc]
  have hl : left.length = r := by simp [left, r]; omega
  have hr : right.length = r := by simp [right, r]; omega
  have hsub : wordGraphCut f ⊆ wordBasicEdges L N := Finset.filter_subset _ _
  have hcore : ∀ d ∈ wordGraphCut f, ∃ a b : List Bool, d.1.val = a ++ core ++ b := fun d hd =>
    wordContour_protected_core (wordGraphCut f) hsub e he hconn core left right ha (by omega) (by omega) d hd
  have hcut : ∀ d ∈ wordGraphCut f, d.1.val.length ≤ e.1.val.length + r := fun d hd => by
    obtain ⟨p, hp⟩ := wordContour_product_locality (wordGraphCut f) hsub e he hconn d hd
    have := endWord_walk_length_bound p; omega
  have hn : e.1 ≠ boundedFoodRoot L N := by simpa [wordBasicEdges] using hsub he
  have hLM : L < e.1.val.length + r := by
    rcases e.1.2 with h | h
    · exact (hn (Subtype.ext h)).elim
    · have := h.1; omega
  have hlen : e.1.val.length = core.length + 2 * r := by simp [core, r]; omega
  have hb : 0 < (wordGraphCut f).card := Finset.card_pos.mpr ⟨e, he⟩
  refine ⟨fun v hv => ?_, fun hminor s hs => ?_⟩
  · have hvl := wordCut_nonfood_length_le f hLM hcut core hne hcore v hv
    obtain ⟨p, hp⟩ := endWord_common_core_walk v.val e.1.val core
      (wordCut_nonfood_side_contains_core f core hcore v hv) ⟨left, right, ha⟩
    exact ⟨p, by omega⟩
  · have hN := wordFoodSide_minor_cap_bound f hLM hcut core hne hcore (3 * r) (by omega) hminor
    have heN := boundedFoodWord_length_le e.1
    obtain ⟨p, hp⟩ := endWord_common_core_walk s e.1.val [] ⟨[], s, by simp⟩ ⟨[], e.1.val, by simp⟩
    simp only [List.length_nil, mul_zero, add_zero] at hp
    exact ⟨p, by omega⟩

end HordijkSteelThreshold
