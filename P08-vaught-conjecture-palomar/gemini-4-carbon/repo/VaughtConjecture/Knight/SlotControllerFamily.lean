/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.VisibleOrderInterpolation
public import Mathlib.Logic.Relation
public import VaughtConjecture.Knight.SourceCode
public import VaughtConjecture.Knight.MixedGradeInterpolation
public import VaughtConjecture.Knight.FreeDiagonal

@[expose] public section

namespace VaughtConjecture.Knight.SeparatedGradeOne

open AmalgamationPlan Transform Value ExtOrd FullRowLifting

/-- The fixed offset-one source form. -/
noncomputable def band (n : ℕ) : ExtOrd := ofOrd (Ordinal.omega0 * n + (1 : ℕ))

theorem band_visible (n : ℕ) : SelfVis 1 (band n) := by
  rw [band, selfVis_ofOrd_iff]
  exact (finitePart_mul_add n 1).ge

theorem band_coded (n k : ℕ) : IsCodedLabel k (band n) :=
  Or.inr ⟨n, 1, by omega, rfl⟩

theorem band_mono {m n : ℕ} (h : m ≤ n) : band m ≤ band n := by
  apply ofOrd_le_ofOrd.mpr
  gcongr

theorem band_floor (n : ℕ) : blockFloor (band n) = ofOrd (Ordinal.omega0 * n) := by
  rw [band, blockFloor_ofOrd, limitPart_mul_add n 1]

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

end VaughtConjecture.Knight.SeparatedGradeOne

namespace VaughtConjecture.Knight.FreshSourceSlots

open Transform Value ExtOrd SeparatedGradeOne

local notation "band" => SeparatedGradeOne.band

theorem band_lt {m n : ℕ} (h : m < n) : band m < band n :=
  ofOrd_lt_ofOrd.mpr ((code_add_lt_mul (Nat.cast_lt.mpr h) 1).trans_le le_self_add)

theorem band_le_iff (m n : ℕ) : band m ≤ band n ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt (band_lt (not_le.mp hn))) h
  · exact band_mono



section Decoder

variable {X : Type*} [Fintype X]




end Decoder

section Slots

variable {X : Type*} [Fintype X]






end Slots

end VaughtConjecture.Knight.FreshSourceSlots

namespace VaughtConjecture.Knight.SlotControllerFamily

open Transform Value ExtOrd FreshSourceSlots

/-- Bottom occurrence, fresh occurrence, old levels, and the slot controllers. -/
abbrev Point (n : ℕ) := Option (Option (Fin n)) ⊕ Fin (n + 1)









set_option maxHeartbeats 1200000 in
-- The finite point-class and directed-cross cases require many Presburger branches.

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
  simp only [value, ite_eq_right hi, ite_eq_right hj, band_le_iff]









end VaughtConjecture.Knight.SlotControllerFamily
