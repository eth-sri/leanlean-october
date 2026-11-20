/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeOne

/-! # Grade two of the coupled semantics' bountifulness: the parameter reduction on the cells

For a labelling `q` respecting the frozen rows `rows₃` on `(univ, 2)`, write `x₀ = q H₀old`,
`Y = q U_S` (the grade-two controller, the unique cell of graded index `(univ, 2)`,
`eq_U_S_of_cell`).  On the actual cells:
* `q s₀new = Y` (`s₀new_eq_U_S_of_respects`): the copy of `s₀` and the controller read the same
  separating source `ω·2+3` at the controller;
* `Y ≤ q U_H` (`U_S_le_U_H_of_respects`): the antitone suppressor at the separating source, read
  at grades one and two;
* **`q s₀old = min x₀ Y`** (`s₀old_eq_min_of_respects`): the controller reads the same source
  `ω·2+2` at the two old witnesses; the antitone suppressor bounds the grade-two probe by the
  grade-one probe, and the controller's own value (at most its grade-two suppressor) gives the
  reverse bound;
* every grade-two proper cell is labelled `⊥` (`proper_two_eq_bot`): its row is `⊥` everywhere;
* `q s₀old = ⊥ → Y = ⊥` (`U_S_eq_bot_of_s₀old`): the sources `ω·2+2` and `ω·2+3` sit one step
  apart in one block (clause 5 at threshold three).
Together with the grade-one triple `(v, x₀, x₁)` on the restriction to `(univ, 1)`, a respecting
labelling of `(univ, 2)` is the triple plus **one high label** `Y ≤ x₁`, with the level-two
witnesses reading `min x₀ Y` and `Y`, the grade-two proper cells `⊥`, and the visibility
constraints (`Y` and `min x₀ Y` self-visible at two) and the bottom coupling.

Not done: the grade-two retuning (`ProperToFull₃Low` at `j = 2`).  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

section GradeTwo

variable {q : D₂.below (Finset.univ, 2) → ExtOrd}

end GradeTwo

end VaughtConjecture.Knight
