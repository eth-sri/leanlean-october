module

public import proofs.HordijkSteelThreshold.WordShortAnchors

public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

variable {L N : ℕ} (f : BoundedFoodWord L N → Bool)

theorem nonfood_label_preimage
    (s : List Bool) (hs : s ∈ actualBinaryWords N)
    (hn : boundedWordLabel f s ≠ f (boundedFoodRoot L N)) :
    ∃ u : BoundedFoodWord L N, u.val = s ∧ f u ≠ f (boundedFoodRoot L N) := by
  rw [mem_actualBinaryWords] at hs
  by_cases hL : L < s.length
  · let u : BoundedFoodWord L N := ⟨s, .inr ⟨hL, hs.2⟩⟩
    exact ⟨u, rfl, by rwa [← boundedWordLabel_eq f u]⟩
  · simp_all [boundedWordLabel]

/-- The complement of the molecular food side is exactly the list image of the nonfood vertices. -/
theorem molecular_food_complement  :
    (actualBinaryWords N \ wordMolecularSide f (f $ boundedFoodRoot L N)).card = (wordNonfoodSide f).card := by
  refine .trans (congrArg Finset.card ?_) $ Finset.card_image_of_injective (f := fun u : BoundedFoodWord L N => u.val)
    _ Subtype.val_injective
  ext s
  simp only [wordMolecularSide, wordNonfoodSide, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hs, hn⟩
    obtain ⟨u, hu, hn⟩ := nonfood_label_preimage f s hs (hn ⟨hs, ·⟩)
    grind
  · rintro ⟨u, hn, rfl⟩
    have := boundedWordLabel_eq f u
    exact ⟨(mem_actualBinaryWords u.val N).mpr ⟨fun h => hn $ congrArg f $ Subtype.ext h,
      boundedFoodWord_length_le u⟩, by simp_all⟩

end HordijkSteelThreshold
