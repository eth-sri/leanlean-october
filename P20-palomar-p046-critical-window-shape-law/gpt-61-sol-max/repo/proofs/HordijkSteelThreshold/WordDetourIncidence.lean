
import proofs.HordijkSteelThreshold.WordParentFibers




namespace HordijkSteelThreshold

/-- The final index j represents a short factor of length j+1. -/
abbrev WordShortKey (L N w : ℕ) := WordBasicEdge L N × Fin w

variable {L N w : ℕ}

variable (d : WordShortKey L N w)

/-- Owner (edge,j) uses its own upper short reaction and, when needed,
the parent's short reaction of length j. Food parents need no lower reaction. -/
noncomputable def wordDetourLower   :
    Option (WordShortKey L N w) :=
  if d.2.val = 0 ∨ wordEdgeParent d.1 = boundedFoodRoot L N then none
  else some ((wordEdgeParent d.1, d.1.2),
    ⟨d.2.val-1, lt_of_le_of_lt (Nat.sub_le _ _) d.2.isLt⟩)

noncomputable def wordDetourKeys    := {d} ∪ (wordDetourLower d).toFinset



theorem wordDetourLower_details  (d r : WordShortKey L N w)
    (h : wordDetourLower d = some r) :
    wordEdgeParent d.1 = r.1.1 ∧ d.1.2 = r.1.2 ∧
      d.2.val = r.2.val+1 ∧ r.1.1 ≠ boundedFoodRoot L N := by grind [wordDetourLower]

variable (r : WordShortKey L N w)

/-- A lower reaction has at most two owners: its product's two children on
its fixed side. The food root is excluded by the definition, not assumed small. -/
theorem wordDetourLower_fiber_card   :
    (Finset.univ.filter (fun d : _ =>
      wordDetourLower d = some r)).card ≤ 2 := by
  let z0 := fun d : WordShortKey L N w => wordDetourLower d = some r
  by_cases hr : r.1.1 = boundedFoodRoot L N
  · have he : Finset.univ.filter z0 = ∅ := by grind [wordDetourLower]
    rw [he]
    simp
  · let target := Finset.univ.filter fun u : BoundedFoodWord L N =>
        wordEdgeParent (u,r.1.2) = r.1.1
    have hc : (Finset.univ.filter z0).card ≤ target.card := by
      apply Finset.card_le_card_of_injOn fun d : WordShortKey L N w => d.1.1
      · intro d hd
        have hd := wordDetourLower_details d r (Finset.mem_filter.mp hd).2
        simpa [target, ← hd.2.1] using hd.1
      · intro d hd e he hde
        have hd := wordDetourLower_details d r (Finset.mem_filter.mp hd).2
        have he := wordDetourLower_details e r (Finset.mem_filter.mp he).2
        grind

    exact hc.trans (boundedFoodParent_fiber_card r.1.1 hr r.1.2)



end HordijkSteelThreshold
