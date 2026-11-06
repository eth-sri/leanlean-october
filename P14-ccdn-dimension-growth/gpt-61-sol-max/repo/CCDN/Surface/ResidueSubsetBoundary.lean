/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib.Order.Minimal

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith

/-! Finite subset selection for the residue cover. A minimal modulus
crosses its target by at most one prime factor. A change of containment
then occurs across a single deletion edge. -/

public section
namespace CCDN
open Finset

/-- If a finite set `P` of positive integers bounded by `U` has product at least `X > 1`, then
it contains a subset `R` with product at least `X` and less than `U X`. -/
theorem exists_minimal_product_subset (P : Finset ℕ) {X U : ℝ}
    (hX : 1 < X) (hP : ∀ p ∈ P, (0 : ℝ) < p)
    (hU : ∀ p ∈ P, ↑p ≤ U)
    (hprod : X ≤ ∏ p ∈ P, ↑p) :
    ∃ R : Finset ℕ, R ⊆ P ∧ X ≤ ∏ p ∈ R, ↑p ∧
      (∏ p ∈ R, ↑p) < U * X := by
  classical
  obtain ⟨R, hRP, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun R : Finset ℕ => X ≤ ∏ p ∈ R, (p : ℝ)) P hprod
  have hRne : R.Nonempty := nonempty_iff_ne_empty.mpr fun he =>
    (not_le_of_gt hX) (by simpa [he] using hmin.prop)
  have hproper : ∀ T ⊂ R, (∏ p ∈ T, (p : ℝ)) < X :=
    fun _ h => lt_of_not_ge (hmin.not_prop_of_lt h)
  refine ⟨R, hRP, hmin.prop, ?_⟩
  obtain ⟨p, hp⟩ := hRne
  have hmul := mul_lt_mul_of_pos_left (hproper _ (erase_ssubset hp)) (hP p (hRP hp))
  rw [mul_prod_erase R _ hp] at hmul
  exact hmul.trans_le (mul_le_mul_of_nonneg_right (hU p (hRP hp)) (by linarith))

/-- Any property false at the empty node and true at a terminal node
changes across a one-element subset edge. -/
theorem exists_subset_erase_boundary {α : Type*} [DecidableEq α] (R : Finset α)
    (W : Finset α → Prop) (hempty : ¬ W ∅) (hR : W R) :
    ∃ T : Finset α, T ⊆ R ∧ ∃ p ∈ T, W T ∧ ¬ W (T.erase p) := by
  classical
  obtain ⟨T, hTR, hmin⟩ := exists_minimal_le_of_wellFoundedLT W R hR
  obtain ⟨p, hp⟩ : T.Nonempty := nonempty_iff_ne_empty.mpr fun he =>
    hempty (he ▸ hmin.prop)
  exact ⟨T, hTR, p, hp, hmin.prop, hmin.not_prop_of_lt (erase_ssubset hp)⟩

end CCDN
