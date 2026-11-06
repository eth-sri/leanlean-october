module

public import proofs.HordijkSteelThreshold.WordParentFibers

@[expose] public section

namespace HordijkSteelThreshold
open Classical

/-- The final index j represents a short factor of length j+1. -/
abbrev WordShortKey (L N w : ℕ) := WordBasicEdge L N × Fin w

/-- Owner (edge,j) uses its own upper short reaction and, when needed,
the parent's short reaction of length j. Food parents need no lower reaction. -/
noncomputable def wordDetourLower {L N w : ℕ} (d : WordShortKey L N w) :
    Option (WordShortKey L N w) :=
  if d.2.val = 0 ∨ wordEdgeParent d.1 = boundedFoodRoot L N then none
  else some ((wordEdgeParent d.1, d.1.2),
    ⟨d.2.val-1, lt_of_le_of_lt (Nat.sub_le _ _) d.2.isLt⟩)

noncomputable def wordDetourKeys {L N w : ℕ} (d : WordShortKey L N w) :
    Finset (WordShortKey L N w) := {d} ∪ (wordDetourLower d).toFinset

theorem wordDetourKeys_card {L N w : ℕ} (d : WordShortKey L N w) :
    (wordDetourKeys d).card ≤ 2 := by
  unfold wordDetourKeys
  have hc : (wordDetourLower d).toFinset.card ≤ 1 := by
    cases wordDetourLower d <;> simp
  exact (Finset.card_union_le _ _).trans (by simp only [Finset.card_singleton]; omega)

theorem wordDetourLower_details {L N w : ℕ} (d r : WordShortKey L N w)
    (h : wordDetourLower d = some r) :
    wordEdgeParent d.1 = r.1.1 ∧ d.1.2 = r.1.2 ∧
      d.2.val = r.2.val+1 ∧ r.1.1 ≠ boundedFoodRoot L N := by
  unfold wordDetourLower at h
  split_ifs at h with hz
  cases Option.some.inj h
  simp only [not_or] at hz
  exact ⟨rfl, rfl, by dsimp; omega, hz.2⟩

theorem wordDetourKeys_incidence {L N w : ℕ} (r : WordShortKey L N w) :
    (Finset.univ.filter (fun d : WordShortKey L N w => r ∈ wordDetourKeys d)).card ≤ 3 := by
  have hfib : (Finset.univ.filter (fun d : WordShortKey L N w => wordDetourLower d = some r)).card ≤ 2 := by
    by_cases hr : r.1.1 = boundedFoodRoot L N
    · rw [Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun d hd =>
        (wordDetourLower_details d r (Finset.mem_filter.mp hd).2).2.2.2 hr)]; omega
    · refine (Finset.card_le_card_of_injOn (t := Finset.univ.filter (fun u : BoundedFoodWord L N => wordEdgeParent (u, r.1.2) = r.1.1))
        (fun d : WordShortKey L N w => d.1.1) (fun d hd => ?_) (fun d hd e he hde => ?_)).trans ?_
      · obtain ⟨hp, hs, _, _⟩ := wordDetourLower_details d r (Finset.mem_filter.mp hd).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [← hs, Prod.mk.eta] using hp⟩
      · obtain ⟨_, hs, hj, _⟩ := wordDetourLower_details d r (Finset.mem_filter.mp hd).2
        obtain ⟨_, ht, hk, _⟩ := wordDetourLower_details e r (Finset.mem_filter.mp he).2
        exact Prod.ext (Prod.ext hde (hs.trans ht.symm)) (Fin.ext (by omega))
      · cases r.1.2
        · simpa only [wordEdgeParent, Bool.false_eq_true, ↓reduceIte] using boundedFoodLeft_fiber_card r.1.1 hr
        · simpa only [wordEdgeParent, ↓reduceIte] using boundedFoodRight_fiber_card r.1.1 hr
  refine (Finset.card_le_card (t := {r} ∪ Finset.univ.filter fun d => wordDetourLower d = some r)
    fun d hd => ?_).trans ((Finset.card_union_le _ _).trans (by simp; omega))
  rcases (by simpa [wordDetourKeys] using (Finset.mem_filter.mp hd).2) with rfl | hm
  · exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)

end HordijkSteelThreshold
