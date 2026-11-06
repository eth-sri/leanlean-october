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

theorem band_lt {m n} (h : m < n) : band m < band n :=
  ofOrd_lt_ofOrd.mpr ((code_add_lt_mul (Nat.cast_lt.mpr h) 1).trans_le le_self_add)

theorem band_le_iff m n : band m ≤ band n ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt (band_lt (not_le.mp hn))) h
  · exact band_mono

end VaughtConjecture.Knight.FreshSourceSlots
