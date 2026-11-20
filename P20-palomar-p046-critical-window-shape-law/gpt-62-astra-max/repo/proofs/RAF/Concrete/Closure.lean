module
public import proofs.RAF.Concrete.PolymerCRS

/-! Ordinary reversible closure: stage, molecule and channel bounds; reachable RAFs. -/

@[expose] public section

namespace RAF.Concrete
variable {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R) (S : Finset R)

theorem mem_step {C : Finset M} {x : M} : x ∈ revClosureStep Q S C ↔ x ∈ C ∨ ∃ r ∈ S,
    (Q.lhs r ⊆ C ∧ x ∈ Q.rhs r) ∨ (Q.rhs r ⊆ C ∧ x ∈ Q.lhs r) := by
  grind [revClosureStep, RevEnabledLhs, RevEnabledRhs]

abbrev Closed (C : Finset M) := ∀ r ∈ S, Q.lhs r ⊆ C ↔ Q.rhs r ⊆ C

lemma closed_iff (C : Finset M) : Closed Q S C ↔ revClosureStep Q S C ⊆ C := by
  simp only [Closed,Finset.subset_iff,mem_step]; grind

lemma revClosureAt_mono_stage : Monotone (revClosureAt Q S) :=
  monotone_nat_of_le_succ fun _ => Finset.subset_union_left

lemma stages_subset {C : Finset M} (hf : Q.food ⊆ C) (hc : Closed Q S C) :
    ∀ k, revClosureAt Q S k ⊆ C := by
  intro k; induction k with
  | zero => exact hf
  | succ k ih => simp only [revClosureAt,Finset.subset_iff,mem_step,Closed] at *; grind

end RAF.Concrete

namespace RAFCriticalWindowQuantitative
open RAF.Concrete

variable {M R : Type*} [Fintype M] [DecidableEq M] (Q : ReversibleCRS M R) (S : Finset R)

def fullClosure : Finset M := revClosureAt Q S (Fintype.card M)

lemma full_fixed : revClosureStep Q S (fullClosure Q S) = fullClosure Q S :=
  by
    let C := revClosureAt Q S
    have gt {k} (h : C (k+1) ≠ C k) : (C k).card < (C (k+1)).card :=
      Finset.card_lt_card (lt_of_le_of_ne Finset.subset_union_left h.symm)
    have bound k (h : C (k+1) ≠ C k) : k < (C (k+1)).card := by
      induction k with
      | zero => have := gt h; omega
      | succ k ih => exact lt_of_le_of_lt (ih fun eq => h (congrArg (revClosureStep Q S) eq)) (gt h)
    by_contra hn; exact (Finset.card_le_univ _).not_gt (bound _ hn)

lemma full_food : Q.food ⊆ fullClosure Q S := revClosureAt_mono_stage Q S (Nat.zero_le _)
lemma full_closed : Closed Q S (fullClosure Q S) := (closed_iff Q S _).mpr (full_fixed Q S).le
lemma full_le {C} (hf : Q.food ⊆ C) (hc : Closed Q S C) : fullClosure Q S ⊆ C :=
  stages_subset Q S hf hc _
lemma full_mem (x : M) : x ∈ fullClosure Q S ↔ ∃ k, x ∈ revClosureAt Q S k :=
  ⟨fun h => ⟨_,h⟩,fun ⟨k,h⟩ => stages_subset Q S (full_food Q S) (full_closed Q S) k h⟩
lemma full_mono : Monotone (fullClosure Q) := fun _ T h =>
  full_le _ _ (full_food Q T) fun r hr => full_closed Q T r (h hr)

end RAFCriticalWindowQuantitative

namespace RAF

def Catalysis (M R : Type*) := M → R → Prop

end RAF

namespace RAF.Concrete

open RAF RAF.Polymer

variable {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)

def RevSeedReaction (r : R) : Prop :=
  Q.lhs r ⊆ Q.food ∨ Q.rhs r ⊆ Q.food

instance revSeedReactionDecidable (r : R) :
    Decidable (RevSeedReaction Q r) := by
  unfold RevSeedReaction
  infer_instance

def RevFoodGenerated (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ k, Q.lhs r ∪ Q.rhs r ⊆ revClosureAt Q S k

def RevReflexivelyAutocatalytic
    (C : Catalysis M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ x k, x ∈ revClosureAt Q S k ∧ C x r

def IsRevRAF (C : Catalysis M R)
    (S : Finset R) : Prop :=
  S.Nonempty ∧ RevFoodGenerated Q S ∧ RevReflexivelyAutocatalytic Q C S

theorem exists_rev_seed_of_foodGenerated (S : Finset R)
    (hne : S.Nonempty) (hfg : RevFoodGenerated Q S) :
    ∃ r ∈ S, RevSeedReaction Q r := by
  by_contra! h
  obtain ⟨r,hr⟩ := hne
  obtain ⟨k,hk⟩ := hfg r hr
  have fixed : Closed Q S Q.food := fun j hj => by have := h j hj; unfold RevSeedReaction at this; tauto
  exact h r hr (.inl ((Finset.union_subset_iff.mp hk).1.trans (stages_subset Q S Finset.Subset.rfl fixed k)))

abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}

end RAF.Concrete

