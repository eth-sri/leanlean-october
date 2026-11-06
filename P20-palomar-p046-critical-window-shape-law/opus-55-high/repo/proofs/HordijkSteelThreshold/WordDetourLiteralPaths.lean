module

public import proofs.HordijkSteelThreshold.WordDetourSource
public import proofs.HordijkSteelThreshold.WordDetourPaths

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

/-- One reversible source step after food contraction, with the other factor
explicitly supplied by food. Reaction IDs remain the literal source IDs. -/
def literalFoodEdge {N : ℕ} (L : ℕ) (S : Finset $ Reaction N)
    (u v : List Bool) : Prop :=
  ∃ a ∈ S, contractFoodWord L (moleculeWord $ reactionProduct a) = u ∧
    ((molLength (reactionLeft a) ≤ L ∧
      contractFoodWord L (moleculeWord $ reactionRight a) = v) ∨
     (molLength (reactionRight a) ≤ L ∧
      contractFoodWord L (moleculeWord $ reactionLeft a) = v))

/-- The detour path is realized entirely by its own literal reversible source
reactions with supplied food factors. No probabilistic assumptions occur. -/
theorem wordDetourSource_reach_parent {L N w : ℕ} (hL : 2*w ≤ L)
    (d : WordShortKey L N w) (hd : d.1.1 ≠ boundedFoodRoot L N) :
    Relation.EqvGen (literalFoodEdge L $ wordDetourSourceReactions hL d)
      (wordShortStart d) (wordEdgeParent d.1).val := by
  refine (wordDetourKeys_reach_parent d).mono fun u v ⟨r, hr, hu, hv⟩ => ?_
  have hr' : r.1.1 ≠ boundedFoodRoot L N := by
    simp only [wordDetourKeys, Finset.mem_union, Option.mem_toFinset] at hr
    rcases hr with hr | hr
    · simp_all
    · exact (wordDetourLower_details d r hr).2.2.2
  refine ⟨_, Finset.mem_biUnion.mpr ⟨r, hr, Option.mem_toFinset.mpr $ dite_eq_right hr'⟩, ?_⟩
  subst hu hv
  rcases r with ⟨⟨v, _ | _⟩, j⟩ <;> simp [sourceShortReaction_product, wordShortStart, wordShortEnd, wordDropShort, sourceShortSplit, ← moleculeWord_length, moleculeWord_reactionRight, moleculeWord_reactionLeft] <;> omega

end HordijkSteelThreshold
