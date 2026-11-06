/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OwnerLocalAlignment
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.CoatomBoundaryExtension

/-! # Canonical owner alignment and ordinary old-boundary completion

The complete field inventory supplies shortness, properness and the tail budget.
V-C's endpoint is a grid endpoint in that inventory, proved from the actual
owner observations. Two old lifting clauses construct the lawful old-boundary
completion. No prospective new controller or new-domain lifting is assumed.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalOwnerBoundary
open Transform Value ExtOrd SharpWitnessComposition OwnerLocalEndpoint CanonicalPairedProfiles CoatomBoundaryExtension

theorem endpoint_grid {X : Type*} [Fintype X] {j : ℕ} {a : X → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (d : X) (hd : a d ≠ ⊥) :
    ∃ b : ℕ, b ≤ 2 * Fintype.card X ∧
      endpoint j (a d) = CanonicalPairedInverse.grid j b := by
  rcases mem_codedAlphabet_iff.mp (inventory_coded X j ha d) with hb | ⟨b, n, hb, _, he⟩
  · exact (hd hb).elim
  have hn : n ≤ j := by
    rcases inventory_short X j ha d with hz | ht | ⟨v, hv, hshort⟩
    · exact (hd hz).elim
    · exact (ha.2 d ht).elim
    · simpa only [← ofOrd_inj.mp (he.symm.trans hv), finitePart_mul_add] using hshort
  refine ⟨b, hb, ?_⟩
  rcases lt_or_eq_of_le hn with hn | hn
  · rw [endpoint, he, extVisibilityReplace_ofOrd, visibilityReplace,
      ite_eq_left (by rwa [finitePart_mul_add]), ordinalReplace, limitPart_mul_add]; rfl
  · rw [endpoint, he, hn, extVisibilityReplace_of_le_finitePart
      (by simp only [finitePart_mul_add, le_refl])]; rfl
