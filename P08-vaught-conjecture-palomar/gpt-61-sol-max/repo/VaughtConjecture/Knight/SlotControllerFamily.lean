/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.SeparatedGradeOneCoding
import VaughtConjecture.Knight.MixedGradeInterpolation
import VaughtConjecture.Knight.FreeDiagonal

/-! # Joint rows for an arbitrary finite family of insertion slots

Old levels occupy even blocks and one independent fresh reading occupies an
odd block. Controllers read each other at their first order disagreement.
The two directed cross-readings need not coincide. All incoming row-family
localities follow from a natural-number source-order identity and explicit
faithful interpolation. No transformation is composed.

This is a grade-one row layer, not a support plan or a bountiful domain.
-/

namespace VaughtConjecture.Knight.SlotControllerFamily

open   ExtOrd

-- The finite point-class and directed-cross cases require many Presburger branches.

noncomputable def value (i : ℕ) : ExtOrd :=
  if i = 0 then ⊥ else SeparatedGradeOne.band i

theorem value_visible i : SelfVis 1 (value i) := by
  unfold value
  split_ifs
  · exact selfVis_bot
  · exact SeparatedGradeOne.band_visible i

theorem value_coded i : IsCodedLabel 1 (value i) := by
  unfold value
  split_ifs
  · exact Or.inl rfl
  · exact SeparatedGradeOne.band_coded i 1

theorem value_le_iff i j : value i ≤ value j ↔ i ≤ j := by simp_all [value, SeparatedGradeOne.band] <;> aesop

