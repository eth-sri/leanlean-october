module

public import proofs.HordijkSteelThreshold.ReversibleRecordWords
public import proofs.HordijkSteelThreshold.InfiniteStaticLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete

def splitPrefixCoordinates (M : ℕ) : Finset (List Bool × ℕ) :=
  (shortBinaryWords M).product (Finset.range (M+1))

@[simp] theorem mem_splitPrefixCoordinates (M : ℕ) (z : List Bool × ℕ) :
    z ∈ splitPrefixCoordinates M ↔ z.1.length ≤ M ∧ z.2 ≤ M := by
  simp [splitPrefixCoordinates,mem_shortBinaryWords]

end HordijkSteelThreshold
