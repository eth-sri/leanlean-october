module

public import Glennie.Compact.NearbyOrbits
public import Glennie.Compact.Sections

@[expose] public section

namespace Glennie.Compact.Sections
open Glennie.Compact.Affine20 Glennie.Compact.FlatOrbit Glennie.Compact.NearbyOrbits
section
structure ClassifiedSections extends SignedSections where
  cover : ∀ b ∈ V, fibre54 b = autOrbit (neg b) ∪ autOrbit (pos b)
theorem SignedSections.disj (d : SignedSections) (b) (hb : b ∈ d.V) :
    Disjoint (autOrbit (d.neg b)) (autOrbit (d.pos b)) := by
  rw [Set.disjoint_left]
  intro T hTN hTP
  have h1 := phiOf_eq_of_mem_autOrbit hTN
  have h2 := phiOf_eq_of_mem_autOrbit hTP
  linarith [d.phiNeg b hb, d.phiPos b hb]

end
end Glennie.Compact.Sections

namespace Glennie.Compact.NearbyOrbitsClosed

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.NearbyOrbits Glennie.Compact.PairNormNearby

section
theorem same_sign_rigidity (T S : Triple)
    (hT : ∀ a, Frame (T a)) (hS : ∀ a, Frame (S a))
    (hL : ledger54 T = ledger54 S)
    (hsign : (phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) :
    ∃ k : CompactAutomorphism, mapAtoms k S = T := by
  have hn : phiOf T ≠ 0 := by rcases hsign with h | h <;> linarith [h.1]
  obtain ⟨hs, hg⟩ := nearby_core T S hT hS hL hn
  apply hg
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · exact h
  · rcases hsign with hs | hs <;> linarith [hs.1, hs.2]

/-- **THE UNCONDITIONAL NEARBY FIBRE CLASSIFICATION.**
`NearbyOrbits.nearby_fibres_two_orbits` (:510) with both of its premises discharged by
`PairNormNearby`. Over an open chart neighbourhood of the flat chart point, every full
54-entry fibre is exactly the disjoint union of the two section orbits under the diagonal
automorphism action, and the twenty-coordinate fibre is the same set.

ORDERED TRIPLES, DIAGONAL ACTION. "Exactly two" counts orbits of ordered triples under one
automorphism applied to all nine atoms. No relabelling is quotiented anywhere. -/
theorem nearby_fibres_two_orbits_unconditional : Nonempty Sections.ClassifiedSections := by
  obtain ⟨d⟩ := Sections.flat_two_sections
  refine ⟨⟨d, ?_⟩⟩
  intro b hb
  apply Set.Subset.antisymm
  · rintro T ⟨hT, hTL⟩
    have hTeqN : ledger54 T = ledger54 (d.neg b) := by rw [hTL, d.ledgerNeg b hb]
    have hTeqP : ledger54 T = ledger54 (d.pos b) := by rw [hTL, d.ledgerPos b hb]
    have hn := PairNormNearby.ne_zero_of_sq_eq_of_ne_zero _ _
      (PairNormNearby.nearby_core (d.neg b) T (d.frameNeg b hb) hT hTeqN.symm
        (ne_of_lt (d.phiNeg b hb))).1 (ne_of_lt (d.phiNeg b hb))
    rcases lt_or_gt_of_ne hn with hn | hp
    · exact Or.inl (NearbyOrbitsClosed.same_sign_rigidity T (d.neg b) hT
        (d.frameNeg b hb) hTeqN (Or.inl ⟨hn, d.phiNeg b hb⟩))
    · exact Or.inr (NearbyOrbitsClosed.same_sign_rigidity T (d.pos b) hT
        (d.framePos b hb) hTeqP (Or.inr ⟨hp, d.phiPos b hb⟩))
  · rintro T (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact ⟨frame_mapAtoms g _ (d.frameNeg b hb), by rw [ledger54_map, d.ledgerNeg b hb]⟩
    · exact ⟨frame_mapAtoms g _ (d.framePos b hb), by rw [ledger54_map, d.ledgerPos b hb]⟩

end
end Glennie.Compact.NearbyOrbitsClosed
