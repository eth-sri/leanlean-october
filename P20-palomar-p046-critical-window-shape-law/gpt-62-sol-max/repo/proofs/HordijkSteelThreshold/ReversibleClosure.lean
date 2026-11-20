module

public import proofs.RAF.Concrete.PolymerCRS
public import Mathlib

@[expose] public section

open RAF.Concrete

def RAFCriticalWindowQuantitative.fullClosure {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) : Finset M := revClosureAt Q S (Fintype.card M)

namespace HordijkSteelThreshold
open Classical RAFCriticalWindowQuantitative RAF.Polymer

variable {M R : Type*} [DecidableEq M] (Q : ReversibleCRS M R)

/-- A pool is closed under the selected reversible channels. -/
abbrev RevClosed (S : Finset R) (C : Finset M) : Prop :=
  ∀ ⦃r⦄, r ∈ S → (Q.lhs r ⊆ C ∨ Q.rhs r ⊆ C) → Q.lhs r ∪ Q.rhs r ⊆ C

@[grind =] theorem mem_revClosureStep_ends (S : Finset R) (C : Finset M) (x : M) :
    x ∈ revClosureStep Q S C ↔ x ∈ C ∨ ∃ r ∈ S,
      (Q.lhs r ⊆ C ∨ Q.rhs r ⊆ C) ∧ x ∈ Q.lhs r ∪ Q.rhs r := by
  simp [revClosureStep, mem_ite, RevEnabledLhs, RevEnabledRhs]
  grind

theorem revClosureAt_subset_closed {Q : ReversibleCRS M R}
    {S : Finset R} {C : Finset M} (hf : Q.food ⊆ C) (hC : RevClosed Q S C) (k : ℕ) :
    revClosureAt Q S k ⊆ C := by
  induction k with
  | zero => assumption
  | succ k ih => grind [revClosureAt]

/-- A deterministic iteration of bounded rank is stationary by the rank bound. -/
theorem stationary_of_rank {A : Type*} (v : ℕ → A) (f : A → A) (hv : ∀ t, v (t+1) = f (v t))
    (rank : A → ℕ) (b : ℕ) (hb : ∀ t, rank (v t) ≤ b)
    (hg : ∀ t, v (t+1) ≠ v t → rank (v t) < rank (v (t+1))) : f (v b) = v b := by
  have hm := monotone_nat_of_le_succ (f := rank ∘ v) (by grind)
  have := Nat.stabilises_of_monotone hm hb (by grind) (Nat.le_succ b)
  grind

theorem revClosureStep_eq_iff (S : Finset R) (C : Finset M) :
    revClosureStep Q S C = C ↔ RevClosed Q S C := by
  constructor
  · grind
  · intro h
    ext x
    grind

variable [Fintype M]

theorem fullClosure_completes {S : Finset R} : RevClosed Q S (fullClosure Q S) :=
  (revClosureStep_eq_iff Q S _).mp <| stationary_of_rank (revClosureAt Q S) (revClosureStep Q S) (fun _ => rfl)
    Finset.card _ (fun _ => Finset.card_le_univ _) fun _ h =>
    Finset.card_lt_card (lt_of_le_of_ne Finset.subset_union_left h.symm)

theorem fullClosure_food (S : Finset R) : Q.food ⊆ fullClosure Q S :=
  monotone_nat_of_le_succ (f := revClosureAt Q S) (fun _ => Finset.subset_union_left) (Nat.zero_le _)

theorem fullClosure_least {Q : ReversibleCRS M R} {S : Finset R} {C : Finset M} (hf : Q.food ⊆ C)
    (hC : RevClosed Q S C) : fullClosure Q S ⊆ C := revClosureAt_subset_closed hf hC _

@[simp] theorem mem_fullClosure (S : Finset R) (x : M) :
    x ∈ fullClosure Q S ↔ ∃ k, x ∈ revClosureAt Q S k :=
  ⟨fun h => ⟨_,h⟩, fun ⟨k,h⟩ => revClosureAt_subset_closed (fullClosure_food Q S) (fullClosure_completes Q) k h⟩

theorem fullClosure_mono : Monotone (fullClosure Q) :=
  fun _ T h => fullClosure_least (fullClosure_food Q T)
    (fun _ hr he => fullClosure_completes Q (h hr) he)

theorem fullClosure_eq_food_of_no_seed (S : Finset R)
    (h : ∀ r ∈ S, ¬ RevSeedReaction Q r) : fullClosure Q S = Q.food :=
  (fullClosure_least Finset.Subset.rfl fun r hr he => (h r hr he).elim).antisymm (fullClosure_food Q S)

/-- Ordinary literal reversible closure with a temporary food cutoff. -/
noncomputable def temporaryReactionClosure {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) :
    Finset (Molecule N) := Finset.univ.filter (fun x => ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS N L) S k)

end HordijkSteelThreshold
