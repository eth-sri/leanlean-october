/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SupportLadderRows

/-! # Removing duplicate shadows from the complete ladder table

The rung-only table keeps every rank of every anchor, including unused ranks
and the spare top rung. Its rows are literal restrictions of
`SupportLadderRows.row`. A positive-rank shadow is a duplicate of its rung;
a rank-zero shadow is forced bottom.

Restriction and the constructed extension are inverse on lawful sections and
commute with every numerical cap. This proves the base-table equivalence
needed by the new43 shadow-elimination audit. It does not construct a
mixed-scope carrier or prove its bountifulness.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.RungOnlyLadder

open Transform Value ExtOrd

abbrev Point (H : ℕ) (Q : Type*) := Q × Fin H

variable {X Q : Type*} {H : ℕ} {profile : Q → X → ℕ}

/-- The literal inclusion retains all rungs, not just represented fields. -/
def toFull (v : Point H Q) : SupportLadderRows.Point H X Q :=
  SupportLadderRows.rung v.1 v.2

def restrict (q : SupportLadderRows.Point H X Q → ExtOrd) : Point H Q → ExtOrd :=
  fun v => q (toFull v)

/-- The rung with the same anchor and positive ceiling as a full-table point. -/
def representative (hbound : ∀ a d, profile a d ≤ H)
    (v : SupportLadderRows.Point H X Q) (hv : 0 < SupportLadderRows.ceiling profile v) :
    Point H Q :=
  (SupportLadderRows.parent v,
    ⟨SupportLadderRows.ceiling profile v - 1, by
      have := SupportLadderRows.ceiling_le hbound v
      omega⟩)

@[simp] theorem representative_parent (hbound : ∀ a d, profile a d ≤ H)
    (v : SupportLadderRows.Point H X Q) (hv : 0 < SupportLadderRows.ceiling profile v) :
    SupportLadderRows.parent (toFull (X := X) (representative hbound v hv)) =
      SupportLadderRows.parent v := rfl

@[simp] theorem representative_ceiling (hbound : ∀ a d, profile a d ≤ H)
    (v : SupportLadderRows.Point H X Q) (hv : 0 < SupportLadderRows.ceiling profile v) :
    SupportLadderRows.ceiling profile (toFull (representative hbound v hv)) =
      SupportLadderRows.ceiling profile v := by
  change SupportLadderRows.ceiling profile v - 1 + 1 = _
  omega

/-- Positive shadows copy their rung; zero shadows are filled with bottom. -/
noncomputable def extend (hbound : ∀ a d, profile a d ≤ H)
    (q : Point H Q → ExtOrd) (v : SupportLadderRows.Point H X Q) : ExtOrd :=
  if hv : 0 < SupportLadderRows.ceiling profile v then
    q (representative hbound v hv) else ⊥

@[simp] theorem extend_toFull (hbound : ∀ a d, profile a d ≤ H)
    (q : Point H Q → ExtOrd) (v : Point H Q) :
    extend hbound q (toFull v) = q v := by
  simp [extend, representative, toFull, SupportLadderRows.rung,
    SupportLadderRows.ceiling, SupportLadderRows.parent]

@[simp] theorem restrict_extend (hbound : ∀ a d, profile a d ≤ H)
    (q : Point H Q → ExtOrd) : restrict (extend hbound q) = q := by
  funext v
  exact extend_toFull hbound q v

end VaughtConjecture.Knight.RungOnlyLadder
