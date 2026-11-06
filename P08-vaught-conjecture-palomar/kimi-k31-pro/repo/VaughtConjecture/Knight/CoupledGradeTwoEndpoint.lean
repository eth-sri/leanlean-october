/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeTwoRetune

/-! # The grade-two endpoint: one sufficiency lemma, the three rules cashed out

**The sufficiency lemma** (`respects_of_shape₂`): a labelling of the full grade-two lower set
`(univ, 2)` in the **value shape** `Shape₂` — the four parameters `(vP, x₀', x₁', H')` at the six
named cells (`x₀'` at the old occurrence, `x₁'` at the copy and the grade-one controller,
`min x₀' H'` at the old level-two witness, `H'` at its copy and the grade-two controller), the
proper value `vP` at the proper grade-one cells, `⊥` at the proper grade-two cells — respects the
frozen rows `rows₃` whenever the parameters are **legal** (`Legal₂`: `vP` grade-one self-visible
and below `x₀'`; `x₀' ≤ x₁'` grade-one self-visible and bottom-coupled; `H' ≤ x₁'` and
`min x₀' H'` grade-two self-visible).  Orderliness is the visibility fields; locality uses the
limit-step witnesses at the three grade-one rows (with `Witness.raise` at `ω·2+2` at the grade-one
controller), the strip witness `Witness.strip` at the two level-two witnesses, and the strip raised
at `ω·2+3` at the grade-two controller — where the bottom case is exactly the coupling
`min x₀' H' = ⊥ → H' = ⊥` (`Legal₂.min_bot`); availability is the case analysis of `two_cases`,
with the new scope facts `not_isProper_of_A_sub`/`not_isProper_of_B_sub` (no proper cell's scope
contains a face) closing the proper grade-two controller cases.  The lemma is proved once and
serves all three retuning rules.

**The endpoint** (`properToFull₃_two`): the grade-two scope-changing case of the coupled
semantics' bountifulness — a respecting labelling of a proper pair `(C, 2)` and one of `(univ, 2)`
agreeing below a grade-two self-visible `γ` on the pair have a common respecting labelling of
`(univ, 2)`, literal on the pair and agreeing with the second below `γ`.  The inputs' constraints
are read off the actual cells (the grade-one triple through the restriction to `(univ, 1)`, the
high label through `CoupledGradeTwoConstraints`); the protected face — old, copy, or neither —
selects the rule (`rule_two_old`, `rule_two_copy`, `rule_two_v`), whose `Retuned` output is legal
(`Retuned.legal`) and whose literal-preservation clauses put `retune₂` in the value shape; capped
agreement is the rule's agreement fields.  `properToFull₃_of_le_two` is the obligation
`ProperToFull₃Low` for every target grade `j ≤ 2`, by the same-grade case at `(univ, i)` followed
by `bountiful_full_scope` up to `(univ, j)`.

Not done: grade three (`ProperToFull₃Low` at `j = 3`), whose duplicate graded indices break the
uniqueness argument used here.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## Scope facts about proper cells -/

section Scopes

end Scopes

/-! ## The sufficiency lemma -/

section Sufficiency

end Sufficiency

/-! ## The grade-two endpoint -/

section Endpoint

end Endpoint

end VaughtConjecture.Knight
