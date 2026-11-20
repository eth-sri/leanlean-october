/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedGradeOneCoding
public import VaughtConjecture.Knight.MixedGradeInterpolation
public import VaughtConjecture.Knight.FreeDiagonal

/-! # A finite family of source slots for an independent grade-one reading

Old source values are ranked once, before any output labels are supplied.
Their nonbottom codes occupy even blocks; odd blocks provide fresh slots.
Every source-ordered old target and every visible fresh target fit one slot.
An explicit finite maximum of step witnesses decodes all targets literally.
Bottom, top, and ties are allowed. There is no composition of transformations.

These are row templates, not jointly consistent controllers. Simultaneous
family incidences, availability, and reference readback remain separate.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FreshSourceSlots

open Transform Value ExtOrd SeparatedGradeOne

local notation "band" => SeparatedGradeOne.band

theorem band_le_iff (m n : ℕ) : band m ≤ band n ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt (ofOrd_lt_ofOrd.mpr (LT.lt.trans_le (code_add_lt_mul (Nat.cast_lt.mpr (not_le.mp hn)) 1) le_self_add))) h
  · exact band_mono

end VaughtConjecture.Knight.FreshSourceSlots
