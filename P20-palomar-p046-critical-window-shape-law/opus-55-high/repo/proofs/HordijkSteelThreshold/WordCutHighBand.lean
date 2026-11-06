module

public import proofs.HordijkSteelThreshold.WordHighBand

@[expose] public section

namespace HordijkSteelThreshold
open Classical

variable {L N : ℕ} (f : BoundedFoodWord L N → Bool)

noncomputable def boundedWordLabel
    (s : List Bool) : Bool :=
  if hs : s = [] ∨ (L < s.length ∧ s.length ≤ N) then f ⟨s, hs⟩
  else f $ boundedFoodRoot L N

theorem boundedWordLabel_eq
    (u : BoundedFoodWord L N) : boundedWordLabel f u.val = f u := by
  unfold boundedWordLabel; exact dite_eq_left u.property


/-- Above every boundary product, both literal parents preserve the cut label. -/
theorem wordCut_above_boundary_parents {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (s : List Bool) (hs : M < s.length) (hN : s.length ≤ N) :
    boundedWordLabel f s = boundedWordLabel f s.tail ∧
    boundedWordLabel f s = boundedWordLabel f s.dropLast := by
  let u : BoundedFoodWord L N := ⟨s, Or.inr ⟨by omega, hN⟩⟩
  have hn : u ≠ boundedFoodRoot L N := fun h => by
    simp [ boundedFoodRoot] at h; grind
  have heq b : f u = boundedWordLabel f (wordEdgeParent (u, b)).val := by
    rw [boundedWordLabel_eq]
    by_contra h
    have hm : (u, b) ∈ wordGraphCut f := by
      simp [wordGraphCut, booleanEdgeCut, wordBasicEdges, hn, h]
    grind
  have := heq true
  have hlong : ¬ s.length ≤ L + 1 := by omega
  simp_all [u, ← boundedWordLabel_eq f u, wordEdgeParent, boundedFoodLeft, foodWordLeft, boundedFoodRight, foodWordRight]

/-- A nonfood-side word cannot be longer than all boundary products when they share a core. -/
theorem wordCut_nonfood_length_le {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (u : BoundedFoodWord L N) (hu : f u ≠ f (boundedFoodRoot L N)) :
    u.val.length ≤ M := by
  by_contra h
  have hN := boundedFoodWord_length_le u
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  let v : BoundedFoodWord L N := ⟨List.replicate M $ !a, Or.inr $ by simp; omega⟩
  have h := highBand_label_constant (boundedWordLabel f) M N (by omega)
    (wordCut_above_boundary_parents f hLM hcut) u.val v.val ⟨by omega, hN⟩ ⟨by simp [v], by simp [v]; omega⟩
  simp only [boundedWordLabel_eq] at h
  refine hu $ h.trans $ wordCut_core_avoiding_root f _ hcore v ?_
  rintro ⟨l, r, he⟩
  have hm : a ∈ v.val := by simp_all
  grind

end HordijkSteelThreshold
