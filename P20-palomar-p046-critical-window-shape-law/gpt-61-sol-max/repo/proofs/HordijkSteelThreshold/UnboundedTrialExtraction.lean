
import proofs.HordijkSteelThreshold.ReversibleMeasurableEvents




namespace HordijkSteelThreshold

def ReversibleUnbounded (L : ℕ) (field : InfiniteSplitEnvironment)  :=
  ∀ K : ℕ, ∃ w, K < w.length ∧ InfiniteReversibleGenerated L field w

end HordijkSteelThreshold
