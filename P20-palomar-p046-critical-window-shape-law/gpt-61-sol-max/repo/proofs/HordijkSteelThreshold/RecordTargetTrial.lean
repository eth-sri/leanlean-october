
import proofs.HordijkSteelThreshold.ReversibleRecordWords
import proofs.HordijkSteelThreshold.InfiniteStaticLaw




namespace HordijkSteelThreshold

def splitPrefixCoordinates (M : ℕ)  :=
  (shortBinaryWords M).product (Finset.range (M+1))

@[simp] theorem mem_splitPrefixCoordinates (M : ℕ) (z : _) :
    z ∈ splitPrefixCoordinates M ↔ z.1.length ≤ M ∧ z.2 ≤ M := by
  simp [splitPrefixCoordinates,mem_shortBinaryWords]

end HordijkSteelThreshold
