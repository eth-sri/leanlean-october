/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-! # Kőnig’s edge colouring argument via Hall’s theorem -/

public section

namespace Konig

open Finset

variable {V : Type*} [Fintype V]

/-- The positive entries of a regular matrix are covered by one permutation per unit of degree. -/
theorem cover (d : ℕ) (A : V → V → ℕ)
    (hr : ∀ i, ∑ j, A i j = d) (hc : ∀ j, ∑ i, A i j = d) :
    ∃ p : Fin d → Equiv.Perm V, ∀ i j, 0 < A i j → ∃ k, p k i = j := by
  classical
  induction d generalizing A with
  | zero => exact ⟨Fin.elim0, by simp_all⟩
  | succ d ih =>
    -- Weighted Hall: the total outgoing weight of a set must fit in its neighbours.
    obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm V, ∀ i, 0 < A i (σ i) := by
      obtain ⟨f, hf, hm⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective
        (fun i j => 0 < A i j)).1 (by
        intro S
        have h (i) (hi : i ∈ S) : ∑ j with ∃ a ∈ S, 0 < A a j, A i j = d + 1 := by
          rw [← hr i]
          exact sum_subset (subset_univ _) (by grind)
        apply Nat.le_of_mul_le_mul_right _ d.succ_pos
        rw [← sum_const_nat h, sum_comm]
        exact sum_le_card_nsmul _ _ _ fun j _ =>
          (sum_le_sum_of_subset (subset_univ S)).trans_eq (hc j))
      exact ⟨Equiv.ofBijective f hf.bijective_of_finite, hm⟩
    -- Removing the chosen matching subtracts one from every row and column sum.
    obtain ⟨p, hp⟩ := ih (fun i j => A i j - if σ i = j then 1 else 0)
      (by
        intro i
        rw [sum_tsub_distrib]
        · simp [hr]
        · grind)
      (by
        intro j
        rw [sum_tsub_distrib]
        · simp [hc, ← σ.eq_symm_apply]
        · grind)
    refine ⟨Fin.cons σ p, ?_⟩
    simp only [Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]
    grind

end Konig
