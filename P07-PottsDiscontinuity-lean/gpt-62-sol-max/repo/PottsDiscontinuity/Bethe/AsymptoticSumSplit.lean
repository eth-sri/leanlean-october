module

public import Mathlib

/-! Splitting a finite product or sum into blocks and reflecting the indices. -/

@[expose] public section

open Finset
namespace PottsDiscontinuity.Bethe

variable {α : Type*} [CommMonoid α]

@[to_additive]
theorem prod_fin_split_block {m a n b : ℕ} (hcount : a + n + b = m) (f : Fin m → α) :
    (∏ j, f j) = (∏ j : Fin a, f ⟨j.val, by omega⟩) *
      (∏ j : Fin n, f ⟨a + j.val, by omega⟩) *
      ∏ j : Fin b, f ⟨a + n + j.val, by omega⟩ := by
  subst m
  rw [Fin.prod_univ_add, Fin.prod_univ_add]
  rfl

@[to_additive]
theorem prod_fin_reflect_block {m a k b : ℕ} (hcount : a + k + b = m)
    (f : Fin m → α) (hsym : ∀ j, f (Fin.rev j) = f j) :
    (∏ j : Fin k, f ⟨a + j.val, by omega⟩) = ∏ j : Fin k, f ⟨b + j.val, by omega⟩ := by
  refine Eq.trans ?_ (Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin k)) (fun j => f ⟨b + j.val, by omega⟩))
  refine prod_congr rfl fun j _ => ?_
  rw [← hsym ⟨a + j.val, by omega⟩]
  congr 1
  apply Fin.ext
  simp only [Fin.revPerm_apply, Fin.val_rev]
  omega

end PottsDiscontinuity.Bethe
