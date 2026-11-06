/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProperBoundarySourceLayer
public import VaughtConjecture.Knight.PairedSlotComparison
public import VaughtConjecture.Knight.CoatomBoundaryExtension

/-! # Constructed paired-decoded sections of a proper boundary layer

The finite controller family, incoming normalization, rows, and selected decoded
sections are constructed from the actual boundary semantics. Retained owners may
have the new grade and arbitrary long source rows. The new rows alone are short.

This is one layer, with every old occurrence in its proper boundary. It supplies
the decoder-to-carrier step of Plan 29, not the induction adding all lower full
indices, arbitrary-ambient lifting, or coatom amalgamation.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.PairedBoundarySections

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition
open PairedSlotEncoding PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ)

/-- All lawful short coded profiles, not a chosen list of displays. Including
non-normalized coded profiles avoids needing idempotence for family membership. -/
def Profile := {p : Cell D → ExtOrd // RespectsSemantics sem p ∧
  (∀ d, p d ∈ ExtOrd.codedAlphabet (2 * Fintype.card (Cell D)) j) ∧ ∀ d, Short j (p d)}

instance : Fintype (Profile sem j) :=
  ((codedLabellings_finite (Cell D) (2 * Fintype.card (Cell D)) j).subset
    (fun _ h => h.2.1)).fintype

def ceiling : ExtOrd :=
  ofOrd (Ordinal.omega0 * (2 * Fintype.card (Cell D) + 1 : ℕ) + j)

theorem grid_bound {h : ExtOrd} (hh : h ∈ sourceGrid j (Fintype.card (Cell D))) :
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

theorem grid_short {h : ExtOrd} (hh : h ∈ sourceGrid j (Fintype.card (Cell D))) :
    Short j h := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact Or.inl rfl
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hh
    exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)

variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (hg : ∀ d : Cell D, D.grade d ≤ j)

variable {G : Finset ExtOrd} {C : ExtOrd}

end
end VaughtConjecture.Knight.PairedBoundarySections
