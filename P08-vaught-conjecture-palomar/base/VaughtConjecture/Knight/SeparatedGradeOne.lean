/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneConservativeLifting

/-! # Actual rows from a separated grade-one source profile

Grade-one rows are literal restrictions of one profile. Other rows are mute.
The profile is visible at grade one, monotone along same-grade availability
requests, and has at most one value in each source block. These are source
conditions, not assumptions of consistency, sections, or bountifulness.

Consistency and all inhabited grade-one lifts follow. The construction is
deliberately restricted: it does not preserve arbitrary pre-existing rows,
and it has no non-mute higher-grade controller.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SeparatedGradeOne

open AmalgamationPlan Transform Value ExtOrd FullRowLifting

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- The source data of the construction; cells are never quotiented by value. -/
structure Profile (D : CellScheme A) where
  source : Cell D → ExtOrd
  visible : ∀ d, SelfVis 1 (source d)
  separated : ∀ d e, blockFloor (source d) = blockFloor (source e) → source d = source e
  available : ∀ d e, D.scope d ⊆ D.scope e → D.grade d = 1 → D.grade e = 1 →
    source d ≤ source e

namespace Profile

variable (F : Profile D)

/-- All rows are actual functions: shared-profile restrictions at grade one,
and constant bottom at the other grades. -/
def rows : Semantics D where
  E c d := if D.grade c = 1 then F.source d.1 else ⊥
  orderly c d := by
    split_ifs with hc
    · have hd : D.grade d.1 = 1 := le_antisymm (hc ▸ d.2.2) (D.grade_pos d.1)
      simpa only [hd] using (F.visible d.1).symm
    · exact (selfVis_bot _).symm

@[simp] theorem row_one {c : Cell D} (hc : D.grade c = 1)
    (d : D.below (D.cell c)) : F.rows.E c d = F.source d.1 := by
  simp only [rows, hc, ↓reduceIte]

@[simp] theorem row_mute {c : Cell D} (hc : D.grade c ≠ 1)
    (d : D.below (D.cell c)) : F.rows.E c d = ⊥ := by
  simp only [rows, hc, ↓reduceIte]

variable {CI BJ : Finset ι × ℕ}

end Profile

end VaughtConjecture.Knight.SeparatedGradeOne
