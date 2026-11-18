module

public import proofs.HordijkSteelThreshold.UnboundedTrialExtraction

@[expose] public section

namespace HordijkSteelThreshold
open Classical

theorem finiteReversibleGenerated_length_le {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : w.length ≤ N := by
  induction h with
  | food _ _ hN => exact hN
  | ligate _ _ _ hN _ _ => exact hN
  | left _ _ _ _ ih => simp only [List.length_append] at ih; omega
  | right _ _ _ _ ih => simp only [List.length_append] at ih; omega

end HordijkSteelThreshold
