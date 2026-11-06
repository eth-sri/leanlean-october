/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.ProperBoundarySourceLayer
import VaughtConjecture.Knight.PairedSlotComparison
import VaughtConjecture.Knight.CoatomBoundaryExtension

/-! # Constructed paired-decoded sections of a proper boundary layer

The finite controller family, incoming normalization, rows, and selected decoded
sections are constructed from the actual boundary semantics. Retained owners may
have the new grade and arbitrary long source rows. The new rows alone are short.

This is one layer, with every old occurrence in its proper boundary. It supplies
the decoder-to-carrier step of Plan 29, not the induction adding all lower full
indices, arbitrary-ambient lifting, or coatom amalgamation.
-/

namespace VaughtConjecture.Knight.PairedBoundarySections

open   ExtOrd  SharpWitnessComposition
open  PairedSlotComparison



variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable  (j : ℕ)

def ceiling :=
  ofOrd (Ordinal.omega0 * (2 * Fintype.card (Cell D) + 1 : ℕ) + j)

theorem grid_bound {h} (hh : h ∈ sourceGrid j (Fintype.card (Cell D))) :
    h ≤ ceiling (D := D) j := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact bot_le
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
    have hb' : b ≤ 2 * Fintype.card (Cell D) + 1 := by
      have := Finset.mem_range.mp hb
      omega
    apply ofOrd_le_ofOrd.mpr
    gcongr

theorem grid_short {h} (hh : h ∈ sourceGrid j (Fintype.card (Cell D))) :
    Short j h := by
  
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact Or.inl rfl
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hh
    exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)


