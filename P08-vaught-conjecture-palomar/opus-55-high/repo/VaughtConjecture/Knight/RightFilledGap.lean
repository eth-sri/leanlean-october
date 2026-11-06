/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrbitPrefixSupport

/-! # Right-filling an unused decoder gap

This is the gap arithmetic from `vc-notes/simplification/note4.md`, Section 2.
For a finite grid `G`, previous ceiling `L`, and next occupied floor `B`, the gap
is filled at `max L (floor G B)`. It stays between the two occupied pieces, reaches
every grid cut below `B`, preserves cap agreement, and introduces no unsupported
orbit or visibility defect.

These facts do not construct the paired normalization or its full decoder.
Matching the occupied groups of two profiles and locating their last common
source-grid cut remain separate obligations of the decoder comparison theorem.
The grid is explicit and finite; no nonexistent maximum below an arbitrary limit
ordinal is used. In the proposed construction it is the finite grid below the
chosen coded ceiling.
-/

@[expose] public section

namespace VaughtConjecture.Knight.RightFilledGap

open Transform Value ExtOrd

section
variable (G : Finset ExtOrd) (B : ExtOrd)

/-- The greatest grid value below the next floor, or bottom if none qualifies. -/
noncomputable def floor  : ExtOrd :=
  G.sup (fun z => if z ≤ B then z else ⊥)

theorem floor_le  : floor G B ≤ B := by
  apply Finset.sup_le
  intro z _
  split_ifs with hz
  · exact hz
  · exact bot_le

end

theorem le_floor {G} {h B} (hh : h ∈ G) (hle : h ≤ B) :
    h ≤ floor G B := by
  unfold floor
  apply Finset.le_sup_of_le hh
  simp only [ite_eq_left hle, le_refl]

/-- A finite maximum creates no extra value between the grid points. -/
theorem floor_eq_bot_or_mem G B :
    floor G B = ⊥ ∨ floor G B ∈ G := by
  apply Finset.sup_induction (p := fun z => z = ⊥ ∨ z ∈ G)
  · exact Or.inl rfl
  · intro a ha b hb
    rcases le_total a b with hab | hba
    · simpa only [sup_eq_right.mpr hab] using hb
    · simpa only [sup_eq_left.mpr hba] using ha
  · intro z hz
    split_ifs
    · exact Or.inr hz
    · exact Or.inl rfl

end VaughtConjecture.Knight.RightFilledGap
