module

public import proofs.HordijkSteelThreshold.WordHighBand

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def boundedWordLabel {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (s : List Bool) : Bool :=
  if hs : s = [] ∨ (L < s.length ∧ s.length ≤ N) then f ⟨s, hs⟩
  else f (boundedFoodRoot L N)

theorem boundedWordLabel_eq {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (u : BoundedFoodWord L N) : boundedWordLabel f u.val = f u := by
  unfold boundedWordLabel; exact dite_eq_left u.property

theorem wordCut_above_boundary_parents {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (s : List Bool) (hs : M < s.length) (hN : s.length ≤ N) :
    boundedWordLabel f s = boundedWordLabel f s.tail ∧
    boundedWordLabel f s = boundedWordLabel f s.dropLast := by
  let u : BoundedFoodWord L N := ⟨s, Or.inr ⟨by omega, hN⟩⟩
  have hn : u ≠ boundedFoodRoot L N := fun h => by
    have := congrArg (fun v : BoundedFoodWord L N => v.val.length) h
    change s.length = 0 at this; omega
  have heq (b : Bool) : f u = f (wordEdgeParent (u, b)) := by
    by_contra h
    have hh := hcut (u, b) (by simp [wordGraphCut, booleanEdgeCut, wordBasicEdges, hn, h])
    change s.length ≤ M at hh; omega
  have hlong : ¬ s.length ≤ L + 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [boundedWordLabel_eq f u, heq false, ← boundedWordLabel_eq f (wordEdgeParent (u, false))]
    simp [boundedFoodLeft, foodWordLeft, wordEdgeParent, u, hlong]
  · rw [boundedWordLabel_eq f u, heq true, ← boundedWordLabel_eq f (wordEdgeParent (u, true))]
    simp [boundedFoodRight, foodWordRight, wordEdgeParent, u, hlong]

theorem wordCut_nonfood_length_le {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (u : BoundedFoodWord L N) (hu : f u ≠ f (boundedFoodRoot L N)) :
    u.val.length ≤ M := by
  by_contra h
  have hN := boundedFoodWord_length_le u
  have hMN : M < N := by omega
  cases core with
  | nil => exact hne rfl
  | cons a t =>
    let v : BoundedFoodWord L N := ⟨List.replicate M (!a), Or.inr (by simpa using And.intro hLM hMN.le)⟩
    have ha : ¬ ∃ l r : List Bool, v.val = l ++ a :: t ++ r := by
      rintro ⟨l, r, he⟩
      have hm : a ∈ v.val := by rw [he]; simp
      cases a <;> simp [v] at hm
    have hconst : f u = f v := by
      simpa only [boundedWordLabel_eq] using highBand_label_constant (boundedWordLabel f) M N hMN
        (wordCut_above_boundary_parents f hLM hcut) u.val v.val ⟨by omega, hN⟩ ⟨by simp [v], by simp [v]; omega⟩
    exact hu (hconst.trans (wordCut_core_avoiding_root f (a :: t) hcore v ha))

end HordijkSteelThreshold
