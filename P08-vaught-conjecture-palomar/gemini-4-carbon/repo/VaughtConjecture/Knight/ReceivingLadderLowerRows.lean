/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReceivingLadderCarrier

/-! # Physical lower rows and extraction on the mixed receiving carrier

The inherited rows are retained on their entire actual domains. Each new
grade-one rung or shadow reads every present original field, the request,
and both eligible ladder copies using the explicit long-rung formula.
These are coded orderly rows, not a supplied lawfulness interface.

On any semantics installing these rows, an arbitrary lawful section of an
actual lower set restricts to the full ladder table. Thus the faithful scalar
chart and the long-rung zero implications apply to physical occurrences.
Upper rows, consistency of the complete scheme, and lifting are separate.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ReceivingLadderCarrier

open Transform Value ExtOrd

variable {L : ℕ} {X Q U : Type*} [Fintype X] [Fintype Q] [Fintype U]
  (C : CellScheme (ι := Fin 2) Finset.univ) (hC : C.plan = privatePlan)

local notation "D" => scheme (L := L) (X := X) (Q := Q) (U := U) C hC
local notation "T" => SupportLadderRows.Point L X Q

/-- Literal old rows with no enlarged domain. -/
noncomputable def inheritedRow (sem : Semantics C) (c : Cell C)
    (d : (D).below ((D).cell (old C hC c))) : ExtOrd :=
  sem.E c (oldArg C hC c d)

theorem inheritedRow_old (sem : Semantics C) (c : Cell C) (d : C.below (C.cell c)) :
    inheritedRow (L := L) (X := X) (Q := Q) (U := U) C hC sem c
      (oldBelow C hC c d) = sem.E c d := by simp only [inheritedRow, oldArg_oldBelow]

theorem inheritedRow_orderly (sem : Semantics C) (c : Cell C) :
    IsOrderly (fun d : (D).below ((D).cell (old C hC c)) => (D).grade d.1)
      (inheritedRow C hC sem c) := by
  intro d
  dsimp only
  rw [← oldArg_grade C hC c d]
  exact sem.orderly c (oldArg C hC c d)

variable (field : Cell C → X) (request : X) (profile : Q → X → ℕ)

/-- A totalized index for row formulas. Upper occurrences never lie below
a grade-one owner, so their default zero is not a semantic constraint. -/
noncomputable def lowerIndex (a : Q) (d : Cell D) : ℕ :=
  match view C hC d with
  | .inl c => profile a (field c)
  | .inr .request => profile a request
  | .inr (.ladder _ v) => SupportLadderRows.index profile a v
  | .inr (.upper _ _ _) => 0
  | .inr .apex => 0

noncomputable def ladderRow (c : T) (d : Cell D) : ExtOrd :=
  SupportLadderRows.source (SupportLadderRows.ceiling profile c)
    (lowerIndex C hC field request profile (SupportLadderRows.parent c) d)

@[simp] theorem ladderRow_old (c : T) (d : Cell C) :
    ladderRow (U := U) C hC field request profile c (old C hC d) =
      SupportLadderRows.source (SupportLadderRows.ceiling profile c)
        (profile (SupportLadderRows.parent c) (field d)) := by
  simp only [ladderRow, lowerIndex, view_old]

@[simp] theorem ladderRow_request (c : T) :
    ladderRow (U := U) C hC field request profile c (added C hC .request) =
      SupportLadderRows.source (SupportLadderRows.ceiling profile c)
        (profile (SupportLadderRows.parent c) request) := by
  simp only [ladderRow, lowerIndex, view_added]

@[simp] theorem ladderRow_ladder (c v : T) (b : Bool) :
    ladderRow (U := U) C hC field request profile c (added C hC (.ladder b v)) =
      SupportLadderRows.row profile c v := by
  simp only [ladderRow, lowerIndex, view_added, SupportLadderRows.row]

theorem ladderRow_orderly (b : Bool) (c : T) :
    IsOrderly (fun d : (D).below ((D).cell (added C hC (.ladder b c))) => (D).grade d.1)
      (fun d => ladderRow C hC field request profile c d.1) := by
  intro d
  dsimp only
  rw [below_ladder_grade C hC b c d]
  exact (SupportLadderRows.source_visible _ _).symm

variable {BJ : Finset (Fin 3) × ℕ} (b : Bool) (hb : GradedLe (scope b, 1) BJ)

end VaughtConjecture.Knight.ReceivingLadderCarrier
