module

public import proofs.RAF.Concrete.SeedGateway
public import proofs.RAF.Polymer.SeedCount

@[expose] public section

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

theorem revSeedReaction_len {n : Nat} {r : Reaction n}
    (h : RevSeedReaction (binaryPolymerCRS n 2) r) :
    (r.2.2.1 + 1 ≤ 2 ∧ r.1.1 - r.2.2.1 ≤ 2) ∨ r.1.1 + 1 ≤ 2 := by
  simpa [RevSeedReaction, binaryPolymerCRS, binaryFood, Finset.insert_subset_iff,
    reactionLeftLength, reactionRightLength, reactionProductLength] using h

theorem card_concrete_gateway_binary_t2 (n : Nat) :
    Fintype.card (PolymerSeedReaction n 2) ≤ 36 := by
  let f (r : PolymerSeedReaction n 2) : PolymerSeedReaction 4 2 :=
    ⟨⟨⟨r.1.1.1, by have := revSeedReaction_len r.2; omega⟩, r.1.2⟩, by
      simpa [RevSeedReaction, binaryPolymerCRS, binaryFood, Finset.insert_subset_iff,
        reactionLeftLength, reactionRightLength, reactionProductLength] using revSeedReaction_len r.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨⟨ai, _⟩, ad⟩, _⟩ ⟨⟨⟨bi, _⟩, bd⟩, _⟩ h
    cases h; rfl
  exact (Fintype.card_le_of_injective f hf).trans_eq (by decide)

end HordijkSteelThreshold
