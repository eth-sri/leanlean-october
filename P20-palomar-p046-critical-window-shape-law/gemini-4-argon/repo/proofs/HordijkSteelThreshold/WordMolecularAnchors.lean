module

public import proofs.HordijkSteelThreshold.WordShortAnchors

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

theorem nonfood_label_preimage {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (s : List Bool) (hs : s ∈ actualBinaryWords N)
    (hn : boundedWordLabel f s ≠ f (boundedFoodRoot L N)) :
    ∃ u : BoundedFoodWord L N, u.val = s ∧ f u ≠ f (boundedFoodRoot L N) := by
  obtain ⟨hsnil, hN⟩ := (mem_actualBinaryWords s N).mp hs
  have hL : L < s.length := by by_contra h; exact hn (by simp [boundedWordLabel, hsnil, h])
  exact ⟨⟨s, Or.inr ⟨hL, hN⟩⟩, rfl, by rwa [← boundedWordLabel_eq f ⟨s, Or.inr ⟨hL, hN⟩⟩]⟩

theorem wordBond_molecular_anchor_radius {L N : ℕ} (f : BoundedFoodWord L N → Bool)
    (hmin : ∀ g : BoundedFoodWord L N → Bool, (wordGraphCut g).Nonempty →
      wordGraphCut g ⊆ wordGraphCut f → wordGraphCut g = wordGraphCut f)
    (e : WordBasicEdge L N) (he : e ∈ wordGraphCut f) (c : Bool)
    (hminor : (wordMolecularSide f c).card ≤ (actualBinaryWords N \ wordMolecularSide f c).card)
    (s : List Bool) (hs : s ∈ wordMolecularSide f c) :
    ∃ p : endWordGraph.Walk s e.1.val, p.length ≤ 64 * (wordGraphCut f).card := by
  have hconn := fun d hd => wordBond_diamond_connected f hmin e d he hd
  by_cases hshort : e.1.val.length ≤ 8 * (wordGraphCut f).card
  · exact wordShortAnchor_radius f e he hconn hshort c hminor s hs
  have hlong := wordLongAnchor_radius f e he hconn (by omega)
  obtain ⟨hsU, hslabel⟩ := Finset.mem_filter.mp hs
  by_cases hc : c = f (boundedFoodRoot L N)
  · subst hc
    have hcomp : actualBinaryWords N \ wordMolecularSide f (f (boundedFoodRoot L N)) =
        (wordNonfoodSide f).image Subtype.val := by
      ext t; refine ⟨fun ht => ?_, fun ht => ?_⟩
      · obtain ⟨htU, htF⟩ := Finset.mem_sdiff.mp ht
        obtain ⟨u, rfl, hn⟩ := nonfood_label_preimage f t htU fun h => htF (Finset.mem_filter.mpr ⟨htU, h⟩)
        exact Finset.mem_image.mpr ⟨u, (mem_wordNonfoodSide f u).mpr hn, rfl⟩
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
        have hn := (mem_wordNonfoodSide f u).mp hu
        exact Finset.mem_sdiff.mpr ⟨(mem_actualBinaryWords u.val N).mpr
          ⟨fun h => hn (congrArg f (Subtype.ext h)), boundedFoodWord_length_le u⟩,
          fun h => hn ((boundedWordLabel_eq f u).symm.trans (Finset.mem_filter.mp h).2)⟩
    have hcard : (actualBinaryWords N \ wordMolecularSide f (f (boundedFoodRoot L N))).card =
        (wordNonfoodSide f).card := hcomp ▸ Finset.card_image_of_injective _ Subtype.val_injective
    have hp := Finset.card_sdiff_add_card_eq_card
      (show wordMolecularSide f (f (boundedFoodRoot L N)) ⊆ actualBinaryWords N from Finset.filter_subset _ _)
    rw [hcard, actualBinaryWords_card] at hp; rw [hcard] at hminor
    exact hlong.2 (by omega) s ((mem_actualBinaryWords s N).mp hsU).2
  · obtain ⟨u, hu, hn⟩ := nonfood_label_preimage f s hsU (hslabel ▸ hc)
    obtain ⟨p, hp⟩ := hlong.1 u hn
    exact ⟨p.copy hu rfl, by simpa using hp⟩

end HordijkSteelThreshold
