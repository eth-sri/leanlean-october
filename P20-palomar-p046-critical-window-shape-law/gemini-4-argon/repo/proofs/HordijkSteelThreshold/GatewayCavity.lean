module

public import proofs.HordijkSteelThreshold.GatewayProbability

@[expose] public section

namespace HordijkSteelThreshold

open RAF.Concrete

theorem revClosureStep_mono {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} {A B : Finset M}
    (hST : S ⊆ T) (hAB : A ⊆ B) :
    revClosureStep Q S A ⊆ revClosureStep Q T B := by
  refine Finset.union_subset_union hAB ((Finset.biUnion_subset_biUnion_of_subset_left _ hST).trans
    (Finset.biUnion_mono fun r _ => Finset.union_subset_union ?_ ?_))
  all_goals
    split_ifs with h1 h2
    · rfl
    · exact (h2 (h1.trans hAB)).elim
    · exact Finset.empty_subset _
    · rfl

theorem revClosureAt_mono_reactions {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} (hST : S ⊆ T) (k : Nat) :
    revClosureAt Q S k ⊆ revClosureAt Q T k := by
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih => exact revClosureStep_mono Q hST ih

end HordijkSteelThreshold
