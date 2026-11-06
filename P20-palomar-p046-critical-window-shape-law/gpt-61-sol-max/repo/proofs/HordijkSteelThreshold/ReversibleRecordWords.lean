
import proofs.HordijkSteelThreshold.UnboundedTrialExtraction




namespace HordijkSteelThreshold

theorem finiteReversibleGenerated_length_le {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : w.length ≤ N := by
  induction h <;> simp_all <;> omega

end HordijkSteelThreshold
