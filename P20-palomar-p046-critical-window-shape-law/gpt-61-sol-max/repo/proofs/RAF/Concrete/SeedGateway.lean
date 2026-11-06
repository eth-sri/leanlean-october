
import proofs.RAF.Concrete.PolymerCRS
import proofs.RAF.Core.CRS




namespace RAF.Concrete

open RAF.Polymer

variable {M R : Type*} [DecidableEq M]

variable (Q : ReversibleCRS M R)

def RevSeedReaction  (r : R)  :=
  Q.lhs r ⊆ Q.food ∨ Q.rhs r ⊆ Q.food

instance revSeedReactionDecidable (Q : ReversibleCRS M R) (r : R) :
    Decidable (RevSeedReaction Q r) := by
  unfold RevSeedReaction
  infer_instance

def RevFoodGenerated  (S : Finset R)  :=
  ∀ r ∈ S, ∃ k, Q.lhs r ∪ Q.rhs r ⊆ revClosureAt Q S k

variable (C : Catalysis M R) (S : Finset R)

def RevReflexivelyAutocatalytic 
      :=
  ∀ r ∈ S, ∃ x k, x ∈ revClosureAt Q S k ∧ C x r

def IsRevRAF    :=
  S.Nonempty ∧ RevFoodGenerated Q S ∧ RevReflexivelyAutocatalytic Q C S

lemma revClosureAt_eq_food_of_no_seed (Q : ReversibleCRS M R) (S : Finset R)
    (h : ∀ r ∈ S, ¬ RevSeedReaction Q r) :
    ∀ k, revClosureAt Q S k = Q.food := by
  intro k
  induction k <;> simp_all [revClosureAt, revClosureStep, RevSeedReaction, RevEnabledLhs, RevEnabledRhs]




abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}

end RAF.Concrete
