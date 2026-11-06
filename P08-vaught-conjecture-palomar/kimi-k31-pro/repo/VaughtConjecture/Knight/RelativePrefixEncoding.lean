/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedSourceDecoder

/-! # Encoding a prescribed face without moving its low prefix

Keep labels at or below a visible cap literally, and put the remaining labels in
a canonically encoded tail above reserved source blocks. This is a faithful,
bottom-reflecting map, not a pointwise patch of unrelated lawful labellings.
Only the new high labels enter the inventory. Its size and the required source
alphabet are explicit; room in an already fixed tower is not automatic.

The decoder-tail construction recovers the original prescribed labels when its
old shifter fixes this prefix. That hypothesis is a genuine restriction, not a
normal form for arbitrary ambient witnesses. The encoder itself constructs no
extension; the final transport lemma consumes a lawful coded lift.
-/

@[expose] public section

namespace VaughtConjecture.Knight.RelativePrefixEncoding

open Transform Value ExtOrd SharpWitnessComposition SourceBlockPadding




section FiniteInventory

variable {X : Type*} [Fintype X]

open Classical in
/-- High occurrences are retained individually when counting the budget. -/
noncomputable def highCells (p : X → ExtOrd) (γ : ExtOrd) : Finset X :=
  Finset.univ.filter (fun d => γ < p d)

open Classical in
/-- Only high proper values need tracking; zero guarantees bottom reflection. -/
noncomputable def inventory (p : X → ExtOrd) (γ : ExtOrd) : Finset Ordinal.{0} :=
  insert 0 ((highCells p γ).image (fun d => ordOf (p d)))

theorem tracked_high (p : X → ExtOrd) (γ : ExtOrd) (d : X) (hd : γ < p d) :
    p d = ⊥ ∨ p d = ⊤ ∨ ∃ α ∈ inventory p γ, p d = ofOrd α := by

  rcases ExtOrd.cases (p d) with h | h | ⟨α, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨α, Finset.mem_insert_of_mem ?_, h⟩)
    exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩,
      by rw [h, ordOf_ofOrd]⟩


