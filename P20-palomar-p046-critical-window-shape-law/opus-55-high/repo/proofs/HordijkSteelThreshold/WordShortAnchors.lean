module

public import proofs.HordijkSteelThreshold.WordMolecularCounts
public import proofs.HordijkSteelThreshold.WordLongCoreAnchors

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- A cut side counted in actual molecules, including each food word separately. -/
noncomputable def wordMolecularSide {L N : ℕ} (f : BoundedFoodWord L N → Bool) (c : Bool) :=
  (actualBinaryWords N).filter $ fun s => boundedWordLabel f s = c

end HordijkSteelThreshold
