/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FreshSourceSlots

/-! # Joint rows for an arbitrary finite family of insertion slots

Old levels occupy even blocks and one independent fresh reading occupies an
odd block. Controllers read each other at their first order disagreement.
The two directed cross-readings need not coincide. All incoming row-family
localities follow from a natural-number source-order identity and explicit
faithful interpolation. No transformation is composed.

This is a grade-one row layer, not a support plan or a bountiful domain.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SlotControllerFamily

open Transform Value ExtOrd FreshSourceSlots

set_option maxHeartbeats 1200000 in
-- The finite point-class and directed-cross cases require many Presburger branches.

noncomputable def value (i : ℕ) : ExtOrd :=
  if i = 0 then ⊥ else SeparatedGradeOne.band i

section
variable (i : ℕ)

theorem value_visible  : SelfVis 1 (value i) := by
  unfold value
  split_ifs
  · exact selfVis_bot 1
  · exact SeparatedGradeOne.band_visible i

theorem value_coded  : IsCodedLabel 1 (value i) := by
  unfold value
  split_ifs
  · exact Or.inl rfl
  · exact SeparatedGradeOne.band_coded i 1

end

theorem value_le_iff i j : value i ≤ value j ↔ i ≤ j := by
  by_cases hi : i = 0
  · simp [value, hi]
  by_cases hj : j = 0
  · simp [value, hi, hj, SeparatedGradeOne.band]
  simp only [value, ite_eq_right hi, ite_eq_right hj, band_le_iff]

end VaughtConjecture.Knight.SlotControllerFamily
