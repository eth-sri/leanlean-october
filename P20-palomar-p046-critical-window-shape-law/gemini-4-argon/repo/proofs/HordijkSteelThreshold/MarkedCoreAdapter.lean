module

public import proofs.HordijkSteelThreshold.MarkedInfiniteLigation
public import proofs.HordijkSteelThreshold.GatewayCavity

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Concrete

theorem revClosureAt_mono_stage {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) {i j : Nat} (hij : i ≤ j) :
    revClosureAt Q S i ⊆ revClosureAt Q S j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ _ _ ih => exact ih.trans Finset.subset_union_left

end HordijkSteelThreshold
