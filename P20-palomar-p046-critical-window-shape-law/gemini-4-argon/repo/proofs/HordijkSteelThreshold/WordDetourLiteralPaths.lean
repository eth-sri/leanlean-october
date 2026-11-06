module

public import proofs.HordijkSteelThreshold.WordDetourSource
public import proofs.HordijkSteelThreshold.WordDetourPaths

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

/-- One reversible source step after food contraction, with the other factor
explicitly supplied by food. Reaction IDs remain the literal source IDs. -/
def literalFoodEdge {N : ℕ} (L : ℕ) (S : Finset (Reaction N))
    (u v : List Bool) : Prop :=
  ∃ a ∈ S, contractFoodWord L (moleculeWord (reactionProduct a)) = u ∧
    ((molLength (reactionLeft a) ≤ L ∧
      contractFoodWord L (moleculeWord (reactionRight a)) = v) ∨
     (molLength (reactionRight a) ≤ L ∧
      contractFoodWord L (moleculeWord (reactionLeft a)) = v))

theorem wordDetourSource_reach_parent {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) (hd : d.1.1 ≠ boundedFoodRoot L N) :
    Relation.EqvGen (literalFoodEdge L (wordDetourSourceReactions hL d))
      (wordShortStart d) (wordEdgeParent d.1).val := by
  suffices ∀ u v, indexedEdgeReach (wordDetourKeys d) wordShortStart wordShortEnd u v →
      Relation.EqvGen (literalFoodEdge L (wordDetourSourceReactions hL d)) u v from
    this _ _ (wordDetourKeys_reach_parent d)
  intro u v path
  induction path with
  | rel u v h =>
    obtain ⟨r, hr, rfl, rfl⟩ := h
    have hrn : r.1.1 ≠ boundedFoodRoot L N := by
      rcases (by simpa [wordDetourKeys] using hr) with rfl | hr
      · exact hd
      · exact (wordDetourLower_details d r hr).2.2.2
    have hspec : ∃ a, wordShortSourceOption hL r = some a ∧
        contractFoodWord L (moleculeWord (reactionProduct a)) = wordShortStart r ∧
        ((molLength (reactionLeft a) ≤ L ∧
          contractFoodWord L (moleculeWord (reactionRight a)) = wordShortEnd r) ∨
         (molLength (reactionRight a) ≤ L ∧
          contractFoodWord L (moleculeWord (reactionLeft a)) = wordShortEnd r)) := by
      unfold wordShortSourceOption; rw [dite_eq_right hrn]
      refine ⟨_, rfl, by simp [wordShortStart], ?_⟩
      have hv := boundedFoodWord_nonroot_length r.1.1 hrn
      have hj := r.2.isLt
      rcases r with ⟨⟨v, side⟩, j⟩; cases side
      · exact Or.inl ⟨by simp [sourceShortSplit]; omega,
          by simp [moleculeWord_reactionRight, sourceShortSplit, wordShortEnd, wordDropShort]⟩
      · exact Or.inr ⟨by rw [← moleculeWord_length]; simp [moleculeWord_reactionRight, sourceShortSplit]; omega,
          by simp [moleculeWord_reactionLeft, sourceShortSplit, wordShortEnd, wordDropShort]⟩
    obtain ⟨a, ha, hp, hf⟩ := hspec
    exact .rel _ _ ⟨a, Finset.mem_biUnion.mpr ⟨r, hr, Option.mem_toFinset.mpr ha⟩, hp, hf⟩
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end HordijkSteelThreshold
