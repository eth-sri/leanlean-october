module

public import proofs.HordijkSteelThreshold.UnboundedTrialExtraction

public section

namespace HordijkSteelThreshold
open Classical

theorem finiteReversibleGenerated_length_le {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : w.length ≤ N := by
  induction h <;> grind

end HordijkSteelThreshold
