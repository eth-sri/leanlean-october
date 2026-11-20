/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-! # List colouring from kernels -/

@[expose] public section

namespace Galvin

open Finset

/-- Every vertex set contains an independent set that absorbs it along outgoing arcs. -/
def HasKernels {α : Type*} (A D : α → α → Prop) : Prop :=
  ∀ S : Finset α, ∃ K ⊆ S, (∀ x ∈ K, ∀ y ∈ K, ¬ A x y) ∧
    ∀ x ∈ S, ∃ y ∈ K, x = y ∨ D x y

/-- Kernel lemma: lists longer than the out-degrees admit a proper list colouring. -/
theorem kernelList {α C : Type*} (A D : α → α → Prop) [DecidableRel D]
    (hK : HasKernels A D) :
    ∀ (U : Finset α) (L : α → Finset C), (∀ x ∈ U, #(U.filter (D x)) < #(L x)) →
      ∃ f : U → C, (∀ x : U, f x ∈ L x) ∧ ∀ x y : U, A x y → f x ≠ f y := by
  classical
  refine strongInduction fun U ih L hL => ?_
  rcases U.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  obtain ⟨c, hc⟩ := card_pos.mp (Nat.zero_lt_of_lt (hL x hx))
  obtain ⟨K, hsub, hind, habs⟩ := hK (U.filter (c ∈ L ·))
  have hKU := hsub.trans (filter_subset _ _)
  obtain ⟨y, hy, -⟩ := habs x (by grind)
  -- Any remaining vertex whose list loses `c` also loses an outgoing neighbour.
  obtain ⟨f, hf, hp⟩ := ih _ (sdiff_ssubset hKU ⟨y, hy⟩) (fun x => (L x).erase c) (by
    intro z hz
    have hs : (U \ K).filter (D z) ⊆ U.filter (D z) := by grind
    have hl := hL z (by grind)
    rw [card_erase_eq_ite]
    split
    · obtain ⟨w, hw, hd⟩ := habs z (by grind)
      have := card_lt_card ((ssubset_iff_of_subset hs).2 ⟨w, by grind⟩)
      omega
    · exact (card_le_card hs).trans_lt hl)
  exact ⟨fun z => if h : (z : α) ∈ K then c else f ⟨z, mem_sdiff.2 ⟨z.2, h⟩⟩,
    by grind⟩

end Galvin
