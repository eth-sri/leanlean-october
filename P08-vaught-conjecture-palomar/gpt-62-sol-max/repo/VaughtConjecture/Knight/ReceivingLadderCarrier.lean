/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SupportLadderRows
public import VaughtConjecture.Knight.RoundedMeetCarrier

/-! # The mixed-scope carrier for the fixed ladder receiver

Keep a two-point private scheme on `{0,1}` and add the request point `2`.
The mixed scopes are `{0,2}` and `{0,1,2}`. This is the new13--new15 geometry
with the private points ordered first. Every rung, shadow, upper leaf and
numerical node has its own occurrence at each mixed scope. The highest row
will be mute. This file constructs geometry, not bountifulness.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderCarrier

open AmalgamationPlan

def privatePlan : Finset (Finset (Fin 2)) := {∅, {0}, {1}, Finset.univ}

def plan : Finset (Finset (Fin 3)) :=
  {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, Finset.univ}

theorem privatePlan_isPlan : Plan.IsPlan Finset.univ privatePlan := by
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]
  refine Plan.IsPlan.step (a := 0) (b := 1) (Q := {∅, {1}}) (R := {∅, {0}})
    (by decide) (by decide) (by decide) ?_ ?_ (by decide) (by decide) (by decide)
  · rw [show ({0, 1} : Finset (Fin 2)).erase 0 = {1} by decide]
    exact Plan.IsPlan.singleton 1
  · rw [show ({0, 1} : Finset (Fin 2)).erase 1 = {0} by decide]
    exact Plan.IsPlan.singleton 0

theorem isPlan : Plan.IsPlan Finset.univ plan := by
  have he : plan = RoundedMeetCarrier.plan (1 : Fin 2) privatePlan := by decide
  rw [he]
  exact RoundedMeetCarrier.isPlan privatePlan_isPlan 1 (by decide)

def scope : Bool → Finset (Fin 3)
  | false => {0, 2}
  | true => Finset.univ

@[simp] theorem fresh_scope (b : Bool) : (2 : Fin 3) ∈ scope b := by cases b <;> decide

/-- No auxiliary is identified with its parent or with its other-scope copy. -/
inductive Added (L : ℕ) (X Q U : Type*)
  | request
  | ladder (full : Bool) (v : SupportLadderRows.Point L X Q)
  | upper (full : Bool) (a : U) (node : Bool)
  | apex
  deriving Fintype

variable {L : ℕ} {X Q U : Type*}

def newIndex : Added L X Q U → Finset (Fin 3) × ℕ
  | .request => ({2}, 1)
  | .ladder b _ => (scope b, 1)
  | .upper b _ _ => (scope b, 2)
  | .apex => (Finset.univ, 3)

theorem newIndex_mem (x : Added L X Q U) : newIndex x ∈ Plan.gradedPlan plan := by
  cases x with
  | request => dsimp only [newIndex]; decide
  | ladder b _ => cases b <;> dsimp only [newIndex] <;> decide
  | upper b _ _ => cases b <;> dsimp only [newIndex] <;> decide
  | apex => dsimp only [newIndex]; decide

theorem newIndex_fresh (x : Added L X Q U) : (2 : Fin 3) ∈ (newIndex x).1 := by
  cases x with
  | request => dsimp only [newIndex]; decide
  | ladder b _ => exact fresh_scope b
  | upper b _ _ => exact fresh_scope b
  | apex => exact Finset.mem_univ _

variable [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)

include hC in
theorem old_face_iff (B : Finset (Fin 2)) :
    B.image Fin.castSuccEmb ∈ plan ↔ B ∈ C.plan := by
  rw [hC]
  exact (by decide : ∀ B : Finset (Fin 2),
    B.image Fin.castSuccEmb ∈ plan ↔ B ∈ privatePlan) B

noncomputable def scheme : CellScheme (ι := Fin 3) Finset.univ :=
  CellScheme.extendOneWith C plan isPlan (old_face_iff C hC)
    (newIndex (L := L) (X := X) (Q := Q) (U := U)) newIndex_mem

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC

def old (c : Cell C) : Cell D := Fin.castAdd (Fintype.card (Added L X Q U)) c

noncomputable def added (x : Added L X Q U) : Cell D :=
  Fin.natAdd C.card ((Fintype.equivFin (Added L X Q U)) x)

@[simp] theorem old_index (c : Cell C) :
    (D).cell (old (L := L) (X := X) (Q := Q) (U := U) C hC c) =
      ((C.scope c).image Fin.castSuccEmb, C.grade c) :=
  CellScheme.extendOneWith_cell_castAdd c

@[simp] theorem added_index (x : Added L X Q U) :
    (D).cell (added C hC x) = newIndex x := by
  unfold added scheme
  rw [CellScheme.extendOneWith_cell_natAdd, Equiv.symm_apply_apply]

theorem old_injective : Function.Injective (old (L := L) (X := X) (Q := Q) (U := U) C hC) := by
  intro a b h
  have he := congrArg Fin.val h
  exact Fin.ext he

theorem cell_cases (d : Cell D) :
    (∃ c, d = old C hC c) ∨ ∃ x, d = added C hC x := by
  induction d using Fin.addCases with
  | left c => exact Or.inl ⟨c, rfl⟩
  | right j =>
    exact Or.inr ⟨(Fintype.equivFin (Added L X Q U)).symm j,
      congrArg (Fin.natAdd C.card) ((Fintype.equivFin (Added L X Q U)).apply_symm_apply j).symm⟩

/-- Decode the occurrence tag without identifying either mixed-scope copy. -/
noncomputable def view : Cell D → Cell C ⊕ Added L X Q U :=
  Fin.addCases Sum.inl (fun j => Sum.inr ((Fintype.equivFin (Added L X Q U)).symm j))

@[simp] theorem view_old (c : Cell C) :
    view (L := L) (X := X) (Q := Q) (U := U) C hC (old C hC c) = Sum.inl c := by
  simp only [view, old, Fin.addCases_left]

@[simp] theorem view_added (x : Added L X Q U) :
    view C hC (added C hC x) = Sum.inr x := by
  simp only [view, added, Fin.addCases_right, Equiv.symm_apply_apply]

def oldBelow (c : Cell C) (d : C.below (C.cell c)) :
    (D).below ((D).cell (old C hC c)) :=
  ⟨old C hC d.1, by
    rw [old_index, old_index]
    exact ⟨Finset.image_subset_image d.2.1, d.2.2⟩⟩

/-- Every argument below an inherited owner is inherited; none of the
new rung, shadow or upper occurrences enters an old row's domain. -/
theorem below_old (c : Cell C) (d : (D).below ((D).cell (old C hC c))) :
    ∃ a : C.below (C.cell c), oldBelow C hC c a = d := by
  rcases cell_cases C hC d.1 with ⟨a, ha⟩ | ⟨x, hx⟩
  · have hd := d.2
    rw [ha, old_index, old_index] at hd
    exact ⟨⟨a, (Finset.image_subset_image_iff Fin.castSuccEmb.injective).mp hd.1, hd.2⟩,
      Subtype.ext ha.symm⟩
  · have hd := d.2.1
    rw [hx, added_index, old_index] at hd
    obtain ⟨a, _, he⟩ := Finset.mem_image.mp (hd (newIndex_fresh x))
    have hh := congrArg Fin.val he
    have ha := a.isLt
    change a.val = 2 at hh
    omega

noncomputable def oldArg (c : Cell C) (d : (D).below ((D).cell (old C hC c))) :
    C.below (C.cell c) := Classical.choose (below_old C hC c d)

theorem oldArg_spec (c : Cell C) (d : (D).below ((D).cell (old C hC c))) :
    oldBelow C hC c (oldArg C hC c d) = d :=
  Classical.choose_spec (below_old C hC c d)

@[simp] theorem oldArg_oldBelow (c : Cell C) (d : C.below (C.cell c)) :
    oldArg (L := L) (X := X) (Q := Q) (U := U) C hC c (oldBelow C hC c d) = d := by
  apply Subtype.ext
  apply old_injective (L := L) (X := X) (Q := Q) (U := U) C hC
  exact congrArg Subtype.val (oldArg_spec C hC c (oldBelow C hC c d))

theorem oldArg_grade (c : Cell C) (d : (D).below ((D).cell (old C hC c))) :
    C.grade (oldArg C hC c d).1 = (D).grade d.1 := by
  have he := congrArg Subtype.val (oldArg_spec C hC c d)
  have hg := congrArg (fun z : Cell D => ((D).cell z).2) he
  simpa only [oldBelow, old_index, CellScheme.grade] using hg

@[simp] theorem ladder_grade (b : Bool) (v : SupportLadderRows.Point L X Q) :
    (D).grade (added C hC (.ladder b v)) = 1 :=
  congrArg Prod.snd (added_index C hC (.ladder b v))

theorem below_ladder_grade (b : Bool) (v : SupportLadderRows.Point L X Q)
    (d : (D).below ((D).cell (added C hC (.ladder b v)))) : (D).grade d.1 = 1 := by
  have hd := d.2.2
  change (D).grade d.1 ≤ (D).grade (added C hC (.ladder b v)) at hd
  rw [ladder_grade] at hd
  exact le_antisymm hd ((D).grade_pos d.1)

end VaughtConjecture.Knight.ReceivingLadderCarrier
