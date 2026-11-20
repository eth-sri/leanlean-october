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

lemma revClosureStep_eq_food_of_no_seed (Q : ReversibleCRS M R) (S : Finset R)
    (h : ∀ r ∈ S, ¬ RevSeedReaction Q r) :
    revClosureStep Q S Q.food = Q.food := by
  have hempty : S.biUnion (fun r =>
      (if RevEnabledLhs Q Q.food r then Q.rhs r else ∅) ∪
      (if RevEnabledRhs Q Q.food r then Q.lhs r else ∅)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨r, hr, hx⟩ := hx
    have hn := h r hr
    have hnl : ¬ RevEnabledLhs Q Q.food r := fun hl => hn (Or.inl hl)
    have hnr : ¬ RevEnabledRhs Q Q.food r := fun hr' => hn (Or.inr hr')
    simp [hnl, hnr] at hx
  simp [revClosureStep, hempty]

lemma revClosureAt_eq_food_of_no_seed (Q : ReversibleCRS M R) (S : Finset R)
    (h : ∀ r ∈ S, ¬ RevSeedReaction Q r) :
    ∀ k, revClosureAt Q S k = Q.food := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [revClosureAt, ih, revClosureStep_eq_food_of_no_seed Q S h]

theorem exists_rev_seed_of_foodGenerated (Q : ReversibleCRS M R) (S : Finset R)
    (hne : S.Nonempty) (hfg : RevFoodGenerated Q S) :
    ∃ r ∈ S, RevSeedReaction Q r := by
  by_contra hexists
  have hnoseed : ∀ r ∈ S, ¬ RevSeedReaction Q r := by
    intro r hr hs
    exact hexists ⟨r, hr, hs⟩
  obtain ⟨r, hr⟩ := hne
  obtain ⟨k, hk⟩ := hfg r hr
  have hc := revClosureAt_eq_food_of_no_seed Q S hnoseed k
  have hl : Q.lhs r ⊆ Q.food := by
    intro x hx
    exact hc ▸ hk (Finset.mem_union_left _ hx)
  exact hnoseed r hr (Or.inl hl)

abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}

end RAF.Concrete
