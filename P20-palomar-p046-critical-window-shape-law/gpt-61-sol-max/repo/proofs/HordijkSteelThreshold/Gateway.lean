
import proofs.RAF.Concrete.SeedGateway
import proofs.RAF.Polymer.Words
import proofs.RAF.Polymer.Reactions



namespace HordijkSteelThreshold

open RAF.Polymer RAF.Concrete

variable {n t : Nat} (r : Reaction n)

/-- In the concrete reversible polymer model, the apparent extra class of
reverse-food gateways adds nothing: a reaction is a gateway exactly when both
canonical split factors are food molecules. -/
theorem revSeedReaction_iff_food_factors  :
    RevSeedReaction (binaryPolymerCRS n t) r ↔
      reactionLeft r ∈ binaryFood n t ∧ reactionRight r ∈ binaryFood n t := by
  have := reaction_length_add r
  simp [RevSeedReaction, binaryPolymerCRS, binaryFood, Finset.insert_subset_iff]
  omega

theorem revSeedReaction_iff_factor_lengths  :
    RevSeedReaction (binaryPolymerCRS n t) r ↔
      reactionLeftLength r ≤ t ∧ reactionRightLength r ≤ t := by
  rw [revSeedReaction_iff_food_factors]
  simp [binaryFood]





end HordijkSteelThreshold
