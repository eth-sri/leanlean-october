module

public import proofs.HordijkSteelThreshold.NucleusAmplification

@[expose] public section

namespace HordijkSteelThreshold

/-- An infinite split-position environment. `openAt w k` records openness of
the ligation producing `w` at split position `k`. -/
abbrev InfiniteSplitEnvironment := List Bool → Nat → Prop

end HordijkSteelThreshold
