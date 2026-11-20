/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedSourceDecoder

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
  classical
  rcases ExtOrd.cases (p d) with h | h | ⟨α, h⟩
  · exact Or.inl h
  · tauto
  · refine Or.inr (Or.inr ⟨α, Finset.mem_insert_of_mem ?_, h⟩)
    exact Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩,
      by rw [h, ordOf_ofOrd]⟩

end FiniteInventory

end VaughtConjecture.Knight.RelativePrefixEncoding
