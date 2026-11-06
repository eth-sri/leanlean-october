/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.OrbitPrefixSupport

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

namespace VaughtConjecture.Knight.RightFilledGap


/-- The greatest grid value below the next floor, or bottom if none qualifies. -/
noncomputable def floor (G : Finset ExtOrd) (B : ExtOrd) : ExtOrd :=
  G.sup (fun z => if z ≤ B then z else ⊥)

theorem floor_le G B : floor G B ≤ B := by
  apply Finset.sup_le
  intro z _
  split_ifs with hz
  · exact hz
  · exact bot_le

theorem le_floor {G} {h B} (hh : h ∈ G) (hle : h ≤ B) :
    h ≤ floor G B := by
  unfold floor
  apply Finset.le_sup_of_le hh
  simp  [ite_eq_left hle, ]

/-- A finite maximum creates no extra value between the grid points. -/
theorem floor_eq_bot_or_mem G B :
    floor G B = ⊥ ∨ floor G B ∈ G := by
  apply Finset.sup_induction (p := fun z => z = ⊥ ∨ z ∈ G)
  · exact Or.inl rfl
  · grind
  · aesop

