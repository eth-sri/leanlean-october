module

public import proofs.HordijkSteelThreshold.ReversibleMeasurableEvents

@[expose] public section

namespace HordijkSteelThreshold
open Classical

def ReversibleUnbounded (L : ℕ) (field : InfiniteSplitEnvironment) : Prop :=
  ∀ K : ℕ, ∃ w, K < w.length ∧ InfiniteReversibleGenerated L field w

end HordijkSteelThreshold
