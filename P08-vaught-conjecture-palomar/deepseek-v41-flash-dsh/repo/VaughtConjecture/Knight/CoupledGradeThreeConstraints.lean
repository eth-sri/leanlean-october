/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeTwoEndpoint

/-! # Grade three of the coupled semantics' bountifulness: the constraints on the cells

The grade-three cells of `D₂` are the two old caps `a₁old`, `a₂old` (both of graded index
`({0,1,2}, 3)`), the copy `b₁new` (index `({1,2,3}, 3)`), and the three fresh full cells `A₁c`,
`A₂c`, `ub₁` (all of index `(univ, 3)`) — `three_cases`, `eq_three_of_cell`.  Availability at
grade three therefore says only that a grade-three label is below *one* of the three controllers'
(`le_controller_of_respects`); graded-index equality identifies nothing.  What identifies the
labels is the actual controllers' rows, which are frozen: `a₁`'s row reads `ω+3` at every
non-proper cell, `a₂`'s reads `ω+4` except `ω+3` at the `a₁` cells, and `b₁`'s (the labelling
`qL`) reads `ω·2+3` at the separated cells, `ω+4` at the old occurrences and the `a₂` cells,
`ω+3` at the `a₁` cells.

For a labelling `q` respecting `rows₃` on `(univ, 3)`, write `z₁ = q A₁c`, `z₂ = q A₂c`,
`w = q ub₁`.  On the actual cells:
* the controllers are ordered, `z₁ ≤ z₂ ≤ w` (`A₁c_le_A₂c_of_respects`, `A₂c_le_ub₁_of_respects`),
  hence every grade-three label is at most `w` (`le_ub₁_of_respects`);
* **the duplicates collapse onto the controllers**: `q b₁new = w` (`b₁new_eq_ub₁_of_respects`),
  `q a₂old = z₂` (`a₂old_eq_A₂c_of_respects`: `b₁`'s row reads `ω+4` at both, so their probes
  against `w` agree, and `z₂ ≤ q a₂old ≤ w`), `q a₁old = z₁` (`a₁old_eq_A₁c_of_respects`: `a₂`'s
  row reads `ω+3` at both, and `q a₁old ≤ q a₂old = z₂`);
* `w ≤ q U_S` (`ub₁_le_U_S_of_respects`: the antitone suppressor at `ω·2+3`);
* **`z₂ = min (q H₀old) w`** (`A₂c_eq_min_of_respects`: `b₁`'s row reads `ω+4` at the old
  occurrence and at `a₂`'s controller, and the grade-one probe is at most the grade-three
  suppressor because `w` is);
* `z₁ = ⊥ → z₂ = ⊥` (`A₂c_eq_bot_of_A₁c`: the sources `ω+3`, `ω+4` one step apart in one block,
  clause 5 at threshold four).
So a respecting labelling of `(univ, 3)` is a respecting labelling of `(univ, 2)` plus **two
labels** `z₁ ≤ w`, with `w ≤ q U_S`, `z₂ = min (q H₀old) w`, `z₁ ≤ z₂`, self-visibility at
three, and the bottom coupling; the six grade-three cells carry `z₁, z₂, w, z₁, z₂, w`.

Not done: the grade-three retuning (`ProperToFull₃Low` at `j = 3`).  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)


/-! ## The cells of grade three -/

section Cells

/-! ### Memberships -/

/-! ### The rows at the grade-three cells -/

end Cells

/-! ## The constraints on a respecting labelling of `(univ, 3)` -/

section Constraints


end Constraints

end VaughtConjecture.Knight
