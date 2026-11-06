/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledNotBountiful

/-! # The single-row repair of the coupled semantics

The frozen `rows₃` is not bountiful (`CoupledNotBountiful`): a bottom proper label forces `b₁`'s
controller to `⊥` through the chain `z₁ ≤ R₃ v`, `z₁ = ⊥ → z₂ = ⊥`, `z₂ = min x₀ w`, where the last
link comes from `b₁`'s controller reading **one** source `ω+4` at the old occurrence and at `a₂`'s
controller.  **The repair** (after the reviewer's research handoff `SOURCE-REPAIR-HANDOFF.md`,
draft #319) changes that one row and nothing else: `qM` reads `ω·2+3` at the two old witnesses
`H₀old`, `s₀old` and `ω·2+4` at the six separated cells (the copies of `H₀`, `s₀`, `b₁` and the
three controllers), and `qL` elsewhere — eight changed entries, no new ordinal block, both new
finite parts fixed by every replacement at thresholds at most three.  `rowsR` is `rows₃` with that
row (`E_R`).  The old witnesses no longer share a source with `a₂`'s controller.

**Acceptance 1 — faces literal, other rows unchanged**: `rowsR_E_of_A`, `rowsR_E_of_B`,
`rowsR_E_of_ne`, `rowsR_E_of_proper_scope`.

**Acceptance 2 — coding and consistency, both directions at the changed cell**: `rowsR_coded`
(finite parts `3`, `4` at grade three); `rowsR_consistent`.  Rows whose cell does not lie above
`b₁`'s controller are consistent as before (`consistentR_of_not_above`, by agreement of the
semantics below them).  Above it lie exactly `a₁`'s and `a₂`'s controllers (the same graded
index) and the mute cell (`ub₁_below_cases`); the **reverse incidences** — those two rows
respecting the repaired row — are the clamp at `ω·2+4` with constant `ω+3`, resp. `ω+4`
(`A₁c_locality_ub₁R`, `A₂c_locality_ub₁R`, through `min_qM_η₁`/`min_qM_γ₀`: the repaired row reads
`a₁`'s, resp. `a₂`'s, row below those caps).  The **forward incidences** — the repaired row as a
labelling of `(univ, 3)` respecting every row (`qM_respects`) — use one new witness shape,
`Witness.idConst` (the identity below a limit cutoff, a self-visible constant above; its bottom
fibre is `{⊥}`, so clause 5 above the grade reduces to the bottom-input case, where both sides
are bottom), raised by `Witness.raise` at `ω·2+2`
(grade-one controller) and `ω·2+3` (grade-two controller).

**Acceptance 3 — both displays**: the prescribed labelling `qL` respects `rowsR`
(`qL_respectsR`; at the changed row by the clamp at `ω·2+4` with constants `ω+4`, `ω·2+3`,
`qL_locality_ub₁R`), and `qL_realizes` is unchanged; the bottom face of the no-go extends
(`bottomFace_extendsR`): `bottomFull` is `3` where the repaired row is in the block at `ω·2` and
`⊥` elsewhere — its grade-two part by the sufficiency lemma `respects_of_shape₂` with parameters
`(⊥, 3, 3, 3)`, its grade-three localities by the all-bottom transformation at the `a₁`/`a₂` cells,
the face's own locality at the copy of `b₁`, and the limit step at `ω·2` at the changed row.

**Transfers**: below grade three the repaired semantics is the frozen one
(`respectsR_iff_low`), so the grade-one and grade-two endpoints transfer
(`properToFullR_of_le_two`), and bountifulness reduces to the scope-changing obligation
`ProperToFullRLow` (`rowsR_isBountiful_of`).

**Acceptance 4 — the grade-three constraints, re-extracted** (for `q` respecting `rowsR` on
`(univ, 3)`).  Surviving, with the same proofs (rows other than the changed one, or its unchanged
entries): `z₁ ≤ z₂ ≤ w`, every grade-three label `≤ w`, the collapses `q b₁new = w`,
`q a₂old = z₂`, `q a₁old = z₁`, `w ≤ q U_S`, the bottom coupling `z₁ = ⊥ → z₂ = ⊥`, the
moving-orbit bound `z₁ ≤ R₃ v` and its sharp form.  **Dead**: `z₂ = min x₀ w`
(`not_A₂c_eq_minR`: the bottom display has `z₂ = ⊥` under `min x₀ w = 3`).  **Newly induced**:
`z₂ ≤ x₀` (`A₂c_le_H₀old_of_respectsR`, `a₂`'s row), hence `z₂ ≤ min x₀ w`
(`A₂c_le_min_of_respectsR`); and the explicit bottom fibre of the changed row at threshold four,
`min x₀ w = ⊥ → w = ⊥` (`ub₁_eq_bot_of_min_botR`: `ω·2+3 ↦ ω·2+4`).

A tested repair candidate with its acceptance tests compiled; **not** a proof of bountifulness.
Not done: the grade-three face obligations of `ProperToFullRLow`.  The no-go for the frozen
`rows₃` stands unchanged.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)


/-! ## The repaired row -/

section Row

/-! ### Acceptance 1: both faces literal, every other row unchanged -/

/-! ### Acceptance 2a: coded -/

end Row

/-! ## Acceptance 2b: consistency, both directions at `b₁`'s controller -/

section Consistency

end Consistency

/-! ## A witness shape: the identity below a limit cutoff, a constant above -/

section IdConst

end IdConst

/-! ## The values of the repaired row against the caps -/

section MinQM

end MinQM

/-! ## Acceptance 2b, continued: the two reverse incidences and the changed row itself -/

section ConsistencyR

end ConsistencyR

/-! ## Acceptance 2b, concluded: the repaired row respects every row below it -/

section RespectR

end RespectR

/-! ## Acceptance 3: the two displays -/

section Displays

/-! ### Display two: the bottom face extends -/

end Displays

/-! ## The transfers: grades one and two are frozen -/

section Transfer

end Transfer

/-! ## Acceptance 4: the grade-three constraints, re-extracted -/

section ConstraintsR


/-! ### Surviving constraints (rows other than `b₁`'s controller's, or unchanged entries) -/

/-! ### Newly induced constraints -/

end ConstraintsR

end VaughtConjecture.Knight
