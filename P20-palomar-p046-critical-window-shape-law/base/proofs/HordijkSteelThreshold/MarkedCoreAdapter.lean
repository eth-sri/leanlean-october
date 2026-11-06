module

public import proofs.HordijkSteelThreshold.MarkedInfiniteLigation
public import proofs.HordijkSteelThreshold.GatewayCavity

@[expose] public section

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- All internally supported split reactions carried by `C`. -/
noncomputable def markedCoreReactions {n : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n)) (C : Finset (Molecule n)) :
    Finset (Reaction n) := by
  classical
  exact Finset.univ.filter fun r =>
    reactionProduct r ∈ C ∧ reactionLeft r ∈ C ∧ reactionRight r ∈ C ∧
      ∃ y ∈ C, Cat y r

@[simp] theorem mem_markedCoreReactions {n : Nat}
    {Cat : Catalysis (Molecule n) (Reaction n)} {C : Finset (Molecule n)}
    {r : Reaction n} :
    r ∈ markedCoreReactions Cat C ↔
      reactionProduct r ∈ C ∧ reactionLeft r ∈ C ∧ reactionRight r ∈ C ∧
        ∃ y ∈ C, Cat y r := by
  classical
  simp [markedCoreReactions]

theorem revClosureAt_subset_succ {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (k : Nat) :
    revClosureAt Q S k ⊆ revClosureAt Q S (k + 1) := by
  intro x hx
  change x ∈ revClosureStep Q S (revClosureAt Q S k)
  exact Finset.mem_union_left _ hx

theorem revClosureAt_mono_stage {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) {i j : Nat} (hij : i ≤ j) :
    revClosureAt Q S i ⊆ revClosureAt Q S j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ j hij ih => exact ih.trans (revClosureAt_subset_succ Q S j)

end HordijkSteelThreshold
