/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith

/-! Finite subset selection for the residue cover. A minimal modulus
crosses its target by at most one prime factor. A change of containment
then occurs across a single deletion edge. -/

namespace CCDN
section
open Finset

/-- If a finite set `P` of positive integers bounded by `U` has product at least `X > 1`, then
it contains a nonempty subset `R` with product at least `X` and less than `U X`, all of whose
proper subsets have product less than `X`. -/
theorem exists_minimal_product_subset (P : Finset ℕ) {X U : ℝ}
    (hX : 1 < X) (hP : ∀ p ∈ P, (0 : ℝ) < p)
    (hU : ∀ p ∈ P, (p : ℝ) ≤ U)
    (hprod : X ≤ ∏ p ∈ P, (p : ℝ)) :
    ∃ R : Finset ℕ, R ⊆ P ∧ X ≤ ∏ p ∈ R, (p : ℝ) ∧
      (∀ T ⊂ R, (∏ p ∈ T, (p : ℝ)) < X) ∧
      (∏ p ∈ R, (p : ℝ)) < U * X := by
  let S := P.powerset.filter (fun R : Finset ℕ => X ≤ ∏ p ∈ R, (p : ℝ))
  obtain ⟨R, hRS, hmin⟩ := S.exists_min_image Finset.card (⟨P, mem_filter.mpr ⟨mem_powerset.mpr (Subset.refl _), hprod⟩⟩)
  obtain ⟨hRP, hRX⟩ := mem_filter.mp hRS
  have hRP' := mem_powerset.mp hRP
  have hRne : R.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    grind
  have hproper : ∀ T ⊂ R, (∏ p ∈ T, (p : ℝ)) < X := by
    intro T hTR
    by_contra hn
    have hTS : T ∈ S := mem_filter.mpr
      ⟨mem_powerset.mpr (hTR.subset.trans hRP'), le_of_not_gt hn⟩
    exact (not_le_of_gt (card_lt_card hTR)) (hmin T hTS)
  refine ⟨R, hRP', hRX, hproper, ?_⟩
  obtain ⟨p, hp⟩ := hRne
  have hsmall := hproper (R.erase p) (erase_ssubset hp)
  have hmul := mul_lt_mul_of_pos_left hsmall (hP p (hRP' hp))
  rw [mul_prod_erase R _ hp] at hmul
  exact hmul.trans_le (mul_le_mul_of_nonneg_right (hU p (hRP' hp)) (by linarith))

/-- Any property false at the empty node and true at a terminal node
changes across a one-element subset edge. -/
theorem exists_subset_erase_boundary {α : Type*} [DecidableEq α] (R : Finset α)
    (W : Finset α → Prop) (hempty : ¬ W ∅) (hR : W R) :
    ∃ T : Finset α, T ⊆ R ∧ ∃ p ∈ T, W T ∧ ¬ W (T.erase p) := by
  classical
  let S := R.powerset.filter W
  obtain ⟨T, hTS, hmin⟩ := S.exists_min_image Finset.card (⟨R, mem_filter.mpr ⟨mem_powerset.mpr (Subset.refl _), hR⟩⟩)
  obtain ⟨hTR, hWT⟩ := mem_filter.mp hTS
  have hTne : T.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    grind
  obtain ⟨p, hp⟩ := hTne
  refine ⟨T, mem_powerset.mp hTR, p, hp, hWT, ?_⟩
  intro he
  have herase := mem_filter.mpr
    ⟨mem_powerset.mpr (Subset.trans (erase_subset p T) (mem_powerset.mp hTR)), he⟩
  exact (not_le_of_gt (card_lt_card (erase_ssubset hp))) (hmin _ herase)

