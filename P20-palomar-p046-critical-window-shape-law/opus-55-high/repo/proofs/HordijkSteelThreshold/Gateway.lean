module

public import proofs.RAF.Concrete.SeedGateway
public import proofs.RAF.Polymer.Words
public import proofs.RAF.Polymer.Reactions

public section

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

theorem revSeedReaction_iff_factor_lengths {n t : Nat} (r : Reaction n) :
    RevSeedReaction (binaryPolymerCRS n t) r ↔
      reactionLeftLength r ≤ t ∧ reactionRightLength r ≤ t := by
  have := reaction_length_add r
  simp [RevSeedReaction, binaryPolymerCRS, binaryFood, Finset.insert_subset_iff]
  omega

/-- The concrete gateway count: every gateway is a product of two food
molecules, hence already present at length four. -/
theorem card_concrete_gateway_binary_t2 {n : Nat} :
    Fintype.card (PolymerSeedReaction n 2) ≤ 36 :=
  (Fintype.card_le_of_injective (β := PolymerSeedReaction 4 2) (fun r => ⟨⟨⟨r.1.1.val, by
      have := (revSeedReaction_iff_factor_lengths r.1).mp r.2
      simp [reactionLeftLength, reactionRightLength] at this; omega⟩, r.1.2⟩, by
    simpa [revSeedReaction_iff_factor_lengths, reactionLeftLength, reactionRightLength] using r.2⟩)
    (by rintro ⟨⟨⟨a, _⟩, _⟩, _⟩ ⟨⟨⟨b, _⟩, _⟩, _⟩ h; simp_all)).trans_eq $ by decide

end HordijkSteelThreshold
