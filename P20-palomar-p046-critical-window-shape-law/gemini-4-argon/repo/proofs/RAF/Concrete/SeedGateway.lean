module

public import proofs.RAF.Concrete.PolymerCRS
public import proofs.RAF.Core.CRS

@[expose] public section

namespace RAF.Concrete

open RAF RAF.Polymer

variable {M R : Type*} [DecidableEq M]

def RevSeedReaction (Q : ReversibleCRS M R) (r : R) : Prop :=
  Q.lhs r ⊆ Q.food ∨ Q.rhs r ⊆ Q.food

instance revSeedReactionDecidable (Q : ReversibleCRS M R) (r : R) :
    Decidable (RevSeedReaction Q r) := by
  unfold RevSeedReaction
  infer_instance

def RevFoodGenerated (Q : ReversibleCRS M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ k, Q.lhs r ∪ Q.rhs r ⊆ revClosureAt Q S k

def RevReflexivelyAutocatalytic (Q : ReversibleCRS M R)
    (C : Catalysis M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ x k, x ∈ revClosureAt Q S k ∧ C x r

def IsRevRAF (Q : ReversibleCRS M R) (C : Catalysis M R)
    (S : Finset R) : Prop :=
  S.Nonempty ∧ RevFoodGenerated Q S ∧ RevReflexivelyAutocatalytic Q C S

theorem exists_rev_seed_of_foodGenerated (Q : ReversibleCRS M R) (S : Finset R)
    (hne : S.Nonempty) (hfg : RevFoodGenerated Q S) :
    ∃ r ∈ S, RevSeedReaction Q r := by
  by_contra! h
  have hc (k : ℕ) : revClosureAt Q S k = Q.food := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [revClosureAt, ih, revClosureStep, Finset.union_eq_left]
      refine Finset.biUnion_subset.mpr fun r hr => ?_
      obtain ⟨hl, hr'⟩ := not_or.mp (h r hr)
      simp [RevEnabledLhs, RevEnabledRhs, hl, hr']
  obtain ⟨r, hr⟩ := hne
  obtain ⟨k, hk⟩ := hfg r hr
  exact (not_or.mp (h r hr)).1 (hc k ▸ Finset.subset_union_left.trans hk)

abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}

end RAF.Concrete
