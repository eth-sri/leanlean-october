/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FreshSourceSlots

@[expose] public section

namespace VaughtConjecture.Knight.SlotControllerFamily

open Transform Value ExtOrd FreshSourceSlots

noncomputable def value (i : ℕ) : ExtOrd :=
  if i = 0 then ⊥ else SeparatedGradeOne.band i

theorem value_visible (i : ℕ) : SelfVis 1 (value i) := by
  unfold value
  split_ifs
  · exact selfVis_bot 1
  · exact SeparatedGradeOne.band_visible i

theorem value_coded (i : ℕ) : IsCodedLabel 1 (value i) := by
  unfold value
  split_ifs
  · exact Or.inl rfl
  · exact SeparatedGradeOne.band_coded i 1

theorem value_le_iff (i j : ℕ) : value i ≤ value j ↔ i ≤ j := by
  by_cases hi : i = 0
  · simp [value, hi]
  by_cases hj : j = 0
  · simp [value, hi, hj, SeparatedGradeOne.band]
  simp [value, ite_eq_right hi, ite_eq_right hj, band_le_iff]

end VaughtConjecture.Knight.SlotControllerFamily
