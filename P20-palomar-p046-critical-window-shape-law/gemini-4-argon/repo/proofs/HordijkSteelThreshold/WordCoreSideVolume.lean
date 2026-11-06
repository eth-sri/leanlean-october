module

public import proofs.HordijkSteelThreshold.WordCoreCount
public import proofs.HordijkSteelThreshold.WordCutHighBand

@[expose] public section

namespace HordijkSteelThreshold
open Classical

noncomputable def wordNonfoodSide {L N : ℕ} (f : BoundedFoodWord L N → Bool) :=
  Finset.univ.filter (fun u => f u ≠ f (boundedFoodRoot L N))

@[simp] theorem mem_wordNonfoodSide {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (u : BoundedFoodWord L N) : u ∈ wordNonfoodSide f ↔ f u ≠ f (boundedFoodRoot L N) := by
  simp [wordNonfoodSide]

theorem wordFoodSide_minor_cap_bound {L N M : ℕ} (f : BoundedFoodWord L N → Bool)
    (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (k : ℕ) (hM : M ≤ core.length + k)
    (hminor : (2 ^ (N + 1) - 2) - (wordNonfoodSide f).card ≤ (wordNonfoodSide f).card) :
    N ≤ 2 * (k + 1) := by
  have hc : (wordNonfoodSide f).card < 2 ^ (2 * (k + 1)) := by
    rw [← Finset.card_image_of_injective (wordNonfoodSide f) Subtype.val_injective]
    refine core_containing_words_card_lt _ core k (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
      exact wordCut_nonfood_side_contains_core f core hcore u (Finset.mem_filter.mp hu).2
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hs
      exact (wordCut_nonfood_length_le f hLM hcut core hne hcore u (Finset.mem_filter.mp hu).2).trans hM
  have hp : 0 < (2 : ℕ) ^ N := by positivity
  rw [pow_succ] at hminor
  exact (pow_le_pow_iff_right₀ (by decide : 1 < 2)).mp (by omega)

end HordijkSteelThreshold
