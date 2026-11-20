/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SlotCappedLifting
public import VaughtConjecture.Knight.BranchAvailability

/-! # Installing the slot family on the complete two-point plan

The singleton rows admit independent visible labels. Both slot controllers
are installed at the full grade-one index, with their directed cross-readings
unchanged; the required grade-two cell is mute. All occurrences remain distinct.
This is a first geometric installation, not an iteration or a higher-grade
request construction.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.TwoPointSlots

open AmalgamationPlan Transform Value ExtOrd DonorSlotAssembly

abbrev scheme := BranchAvailability.scheme
abbrev Inventory := Occ Unit

noncomputable def source : Unit → ExtOrd := fun _ => SeparatedGradeOne.band 1

def embed : Inventory → Cell scheme
  | .inl none => 1
  | .inl (some _) => 0
  | .inr j => ⟨j.val + 2, by have h : j.val < 2 := j.isLt; change j.val + 2 < 5; omega⟩

def project (d : Cell scheme) : Inventory :=
  if d = 0 then old () else if d = 1 then fresh else
    controller (if d = 2 then 0 else 1)

theorem below_grade_one {c d : Cell scheme} (hc : c ≠ 4)
    (hd : GradedLe (scheme.cell d) (scheme.cell c)) : scheme.grade d = 1 := by
  have h : ∀ c d : Fin 5, c ≠ 4 → GradedLe (scheme.cell d) (scheme.cell c) →
      scheme.grade d = 1 := by unfold GradedLe; decide
  exact h c d hc hd

noncomputable def table (c d : Cell scheme) : ExtOrd :=
  if c = 4 then ⊥ else if c = 0 ∨ c = 1 then SlotControllerFamily.value 1
  else DonorSlotAssembly.row source (if c = 2 then 0 else 1) (project d)

noncomputable def rows : Semantics scheme where
  E c d := table c d.1
  orderly c d := by
    by_cases hc : c = 4
    · simp only [table, hc, ↓reduceIte, extVisibilityReplace_bot]
    have hg := below_grade_one hc d.2
    change table c d.1 = extVisibilityReplace (table c d.1) (scheme.grade d.1) (scheme.grade d.1)
    rw [hg]
    unfold table
    rw [ite_eq_right hc]
    split
    · exact (SlotControllerFamily.value_visible 1).symm
    · exact ((DonorSlotAssembly.rows_joint source _).1 _).symm

end VaughtConjecture.Knight.TwoPointSlots
