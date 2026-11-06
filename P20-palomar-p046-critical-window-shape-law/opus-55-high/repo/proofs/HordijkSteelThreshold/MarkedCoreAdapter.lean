module

public import proofs.HordijkSteelThreshold.InfiniteLigation
public import proofs.HordijkSteelThreshold.GatewayCavity

public section

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

theorem revClosureAt_mono_stage {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) {i j : Nat} (hij : i ≤ j) :
    revClosureAt Q S i ⊆ revClosureAt Q S j :=
  monotone_nat_of_le_succ (fun _ => Finset.subset_union_left) hij

end HordijkSteelThreshold
