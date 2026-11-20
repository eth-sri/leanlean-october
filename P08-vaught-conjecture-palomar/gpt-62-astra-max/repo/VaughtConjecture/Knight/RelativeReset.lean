/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLift
public import VaughtConjecture.Knight.GradeEnvelope

/-! # The reset direction: prescribe the candidate, release the old high tail

The reviewer's notes7 (`mixed_proper_top_charts.md` §4.2, 2026-09-19), on the general-cap
relative data.  The private context is identified with the candidate's root along `φ`, is
bountiful, and its cells may have grades above the cap's grade `N`.

**`lift_reset`.**  Given an allowed pair `(u, v)` and any lawful candidate prescription `v'`
agreeing with `v` below `γ`, first install the prescribed root into `u` by the private
context's bountifulness (retaining every private `γ`-reading), then cap every private cell
of grade at least `N` at `γ` (`high_tail_release`).  The result `u'` is lawful, has the
literal root `v'|_B` (root cells have grade below `N`), agrees with `u` below `γ`, and reads
`u'(C) ≤ γ`; so in the class every correctness relation is evaluated below `γ`, where the
retained readings decide it (`correct_of_cap_le`).  At `γ = ⊥` the cap becomes bottom and
the class is inactive.

**Cap visibility at the target grade.**  The comparison cap `γ` must be visible at the
private top grade `topA.2`, which may exceed `N`: the tail clipping installs `γ` at every
grade from `N` up to `topA.2`, and orderliness there needs exactly that.  The grade gap
`q < N` (root cells below `N`) is a separate requirement.  Neither is implied by
`SelfVis N γ`.

Both lifts retain the selector's cap (`selector_cap_agree`), restated here as
`lift_reset_selector` and `relative_lift_selector`.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ] {A : Finset ιA} {Q : Finset ιQ}
  {DA : CellScheme A} {semA : Semantics DA} {DQ : CellScheme Q} {semQ : Semantics DQ}

/-- **The reset data**: the private context's root and top indices, the identification of
the candidate's root with the private root (compatible with `κ`), lawfulness transport of
candidate labellings to private root sections, and the private context's bountifulness.
Root cells have grade below `N`; the private top grade may exceed `N`. -/
structure ResetData (X : RelativeData DA semA DQ semQ) where
  rootA : Finset ιA × ℕ
  topA : Finset ιA × ℕ
  rootA_mem : rootA ∈ Plan.gradedPlan DA.plan
  topA_mem : topA ∈ Plan.gradedPlan DA.plan
  rootA_le : GradedLe rootA topA
  rootA_ne : rootA ≠ topA
  below_topA : ∀ d, GradedLe (DA.cell d) topA
  /-- The grade gap: root cells lie strictly below the cap's grade. -/
  rootA_lt_N : rootA.2 < X.req.N
  /-- The identification of the two roots. -/
  φ : DQ.below X.root ≃ DA.below rootA
  φ_κ : ∀ r, (φ r).1 = (X.κ r).1
  /-- Lawful candidate labellings restrict to lawful private root sections. -/
  respects_φ' : ∀ v : Cell DQ → ExtOrd, RespectsSemantics semQ v →
    RespectsSemanticsBelow semA rootA (fun d => v (φ.symm d).1)
  /-- The private context is bountiful. -/
  bountifulA : semA.IsBountiful

namespace ResetData

variable {X : RelativeData DA semA DQ semQ} (Y : ResetData X)

end ResetData

namespace RelativeData

variable (X : RelativeData DA semA DQ semQ)

end RelativeData

end VaughtConjecture.Knight
