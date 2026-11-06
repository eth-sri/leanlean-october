/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Closure

/-!
# Closure from an intersection-closed cofinal family of finite sets

Adapted from the newsimple14 canonical-hulls draft.
No infinite intersection or countability is used.
The predicate is deliberately unbundled: both plan faces and actual supports
use the same least-element lemma.
-/

@[expose] public section

namespace VaughtConjecture.FiniteSupportClosure

variable {M : Type*} [DecidableEq M]

section
variable (P : Finset M → Prop)

/-- A nonempty collection of finite supersets, closed under binary intersection,
has a least member.  Only existence above this particular `S` is required. -/
theorem exists_least (hinter : ∀ A B, P A → P B → P (A ∩ B)) S
    (hcover : ∃ A, P A ∧ S ⊆ A) :
    ∃ A, P A ∧ S ⊆ A ∧ ∀ B, P B → S ⊆ B → A ⊆ B := by
  classical
  have hex : ∃ n, ∃ A, P A ∧ S ⊆ A ∧ A.card = n := by
    obtain ⟨A, hA, hSA⟩ := hcover
    exact ⟨A.card, A, hA, hSA, rfl⟩
  obtain ⟨A, hA, hSA, hcard⟩ := Nat.find_spec hex
  refine ⟨A, hA, hSA, ?_⟩
  intro B hB hSB
  have hSAB : S ⊆ A ∩ B := fun x hx =>
    Finset.mem_inter.mpr ⟨hSA hx, hSB hx⟩
  have hle : A.card ≤ (A ∩ B).card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨A ∩ B, hinter A B hA hB, hSAB, rfl⟩
  have heq : A ∩ B = A :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left hle
  rw [← heq]
  exact Finset.inter_subset_right

section
variable (hinter : ∀ A B, P A → P B → P (A ∩ B)) (hcover : ∀ S, ∃ A, P A ∧ S ⊆ A)

noncomputable def hull (S : Finset M) : Finset M :=
  Classical.choose (exists_least P hinter S (hcover S))

theorem hull_spec S :
    P (hull P hinter hcover S) ∧ S ⊆ hull P hinter hcover S ∧
      ∀ B, P B → S ⊆ B → hull P hinter hcover S ⊆ B :=
  Classical.choose_spec (exists_least P hinter S (hcover S))

/-- The usual closure operator. `IsClosed` is definitionally the original
predicate, rather than a second presentation of closedness. -/
noncomputable def ofCofinalInterClosed  : ClosureOperator (Finset M) :=
  ClosureOperator.ofPred (hull P hinter hcover) P
    (fun S => (hull_spec P hinter hcover S).2.1)
    (fun S => (hull_spec P hinter hcover S).1)
    (fun S B hSB hB => (hull_spec P hinter hcover S).2.2 B hB hSB)

end

end

end VaughtConjecture.FiniteSupportClosure
