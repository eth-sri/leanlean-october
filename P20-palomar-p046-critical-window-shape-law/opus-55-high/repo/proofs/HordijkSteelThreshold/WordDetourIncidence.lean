module

public import proofs.HordijkSteelThreshold.WordParentFibers

@[expose] public section

namespace HordijkSteelThreshold
open Classical

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

noncomputable def wordDetourKeys   :
    Finset (WordShortKey L N w) := {d} ∪ (wordDetourLower d).toFinset

theorem wordDetourKeys_card   :
    (wordDetourKeys d).card ≤ 2 :=
  (Finset.card_union_le _ _).trans (by cases wordDetourLower d <;> simp)


theorem wordDetourLower_details  (d r : WordShortKey L N w)
    (h : wordDetourLower d = some r) :
    wordEdgeParent d.1 = r.1.1 ∧ d.1.2 = r.1.2 ∧
      d.2.val = r.2.val+1 ∧ r.1.1 ≠ boundedFoodRoot L N := by
  unfold wordDetourLower at h
  grind

variable (r : WordShortKey L N w)

/-- A lower reaction has at most two owners: its product's two children on
its fixed side. The food root is excluded by the definition, not assumed small. -/
theorem wordDetourLower_fiber_card   :
    (Finset.univ.filter (fun d : WordShortKey L N w =>
      wordDetourLower d = some r)).card ≤ 2 := by
  by_cases hr : r.1.1 = boundedFoodRoot L N
  · simp [Finset.filter_eq_empty_iff.2 fun d _ hd => (wordDetourLower_details d r hd).2.2.2 hr]
  refine (Finset.card_le_card_of_injOn (fun d => d.1.1)
    (t := Finset.univ.filter fun u => wordEdgeParent (u, r.1.2) = r.1.1) (fun d hd => ?_)
    fun d hd e he hde => ?_).trans ?_
  · grind [wordDetourLower_details d r (Finset.mem_filter.mp hd).2]
  · have := wordDetourLower_details d r (Finset.mem_filter.mp hd).2
    have := wordDetourLower_details e r (Finset.mem_filter.mp he).2
    grind
  · rcases r with ⟨⟨u, _ | _⟩, j⟩
    · simpa [wordEdgeParent] using boundedFoodLeft_fiber_card u hr
    · simpa [wordEdgeParent] using boundedFoodRight_fiber_card u hr

/-- At most three detours use a normalized short reaction. This counts all
owners, even the unused root owners, and is uniform in cap and width. -/
theorem wordDetourKeys_incidence   :
    (Finset.univ.filter (fun d : WordShortKey L N w => r ∈ wordDetourKeys d)).card ≤ 3 :=
  (Finset.card_le_card (t := {r} ∪ Finset.univ.filter fun d => wordDetourLower d = some r)
    fun d hd => by simp_all [wordDetourKeys]; aesop).trans
    ((Finset.card_union_le _ _).trans (by have := wordDetourLower_fiber_card r; simp; omega))

end HordijkSteelThreshold
