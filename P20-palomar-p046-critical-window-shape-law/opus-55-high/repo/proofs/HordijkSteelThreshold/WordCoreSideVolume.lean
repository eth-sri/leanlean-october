module

public import proofs.HordijkSteelThreshold.WordCoreCount
public import proofs.HordijkSteelThreshold.WordCutHighBand

@[expose] public section

namespace HordijkSteelThreshold

noncomputable def wordNonfoodSide {L N : ℕ} (f : BoundedFoodWord L N → Bool) :=
  Finset.univ.filter $ fun u => f u ≠ f (boundedFoodRoot L N)

end HordijkSteelThreshold
