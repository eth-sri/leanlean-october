module

public import proofs.RAF.Concrete.PolymerCRS
public import proofs.RAF.Core.CRS

@[expose] public section

namespace RAF.Concrete

open RAF RAF.Polymer

variable {M R : Type*} [DecidableEq M]

section
variable (Q : ReversibleCRS M R)

section
variable (r : R)

def RevSeedReaction   : Prop :=
  Q.lhs r ⊆ Q.food ∨ Q.rhs r ⊆ Q.food

instance revSeedReactionDecidable   :
    Decidable (RevSeedReaction Q r) := by
  unfold RevSeedReaction
  infer_instance

end

variable (S : Finset R)

def RevFoodGenerated   : Prop :=
  ∀ r ∈ S, ∃ k, Q.lhs r ∪ Q.rhs r ⊆ revClosureAt Q S k

section
variable (C : Catalysis M R)

def RevReflexivelyAutocatalytic
     (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ x k, x ∈ revClosureAt Q S k ∧ C x r

def IsRevRAF
    (S : Finset R) : Prop :=
  S.Nonempty ∧ RevFoodGenerated Q S ∧ RevReflexivelyAutocatalytic Q C S

end

lemma revClosureStep_eq_food_of_no_seed
    (h : ∀ r ∈ S, ¬ RevSeedReaction Q r) :
    revClosureStep Q S Q.food = Q.food := by
  have hempty : S.biUnion (fun r =>
      (if RevEnabledLhs Q Q.food r then Q.rhs r else ∅) ∪
      (if RevEnabledRhs Q Q.food r then Q.lhs r else ∅)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    simp at hx
    obtain ⟨r, hr, hx⟩ := hx
    have hn := h r hr
    have hnl : ¬ RevEnabledLhs Q Q.food r := by tauto
    have hnr : ¬ RevEnabledRhs Q Q.food r := fun hr' => hn $ Or.inr hr'
    simp_all
  simp [revClosureStep, hempty]

lemma revClosureAt_eq_food_of_no_seed
    (h : ∀ r ∈ S, ¬ RevSeedReaction Q r) :
    ∀ k, revClosureAt Q S k = Q.food := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [revClosureAt, ih, revClosureStep_eq_food_of_no_seed Q S h]

theorem exists_rev_seed_of_foodGenerated
    (hne : S.Nonempty) (hfg : RevFoodGenerated Q S) :
    ∃ r ∈ S, RevSeedReaction Q r := by
  by_contra hexists
  have hnoseed : ∀ r ∈ S, ¬ RevSeedReaction Q r := by
    simp_all
  obtain ⟨r, hr⟩ := hne
  obtain ⟨k, hk⟩ := hfg r hr
  have hc := revClosureAt_eq_food_of_no_seed Q S hnoseed k
  have hl : Q.lhs r ⊆ Q.food := by
    grind
  tauto

end

abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}

end RAF.Concrete
