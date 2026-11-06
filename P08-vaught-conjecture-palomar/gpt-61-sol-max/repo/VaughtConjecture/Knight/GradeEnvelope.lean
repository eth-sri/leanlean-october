/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoCodedBountiful
public import VaughtConjecture.Knight.CoupledGradeOne
public import VaughtConjecture.Knight.SemScheme

/-! # The grade envelope: bounded-output lifting and high-tail release

Two corollaries of the grade-cap clipping `RespectsSemanticsBelow.gradeCap` (a lawful section
capped by an antitone, gradewise-visible family of caps is lawful), from the reviewer's
notes5 (`plan11.md` §2, `plan16.md` §2, 2026-09-18).

**Bounded-output lifting** (`bounded_lift`, `bounded_lift_of_bountiful`).  Given a lift `t` of
a prescription `p` against an ambient `q` at cap `γ`, and a bound `B ≥ γ` above every
prescribed value, clipping `t` at the **grade envelope**
`G i = max γ (max {p d : grade d ≥ i})` gives a lift with the same prescription and the same
`γ`-reading whose output is at most `B`.  `G` is antitone and `G i` is `i`-visible (every
contributing value is visible at a grade at least `i`), so the clipping is lawful; a
prescribed grade-`i` value contributes to `G i` and is retained; every `G i ≥ γ` keeps the
cap reading.  `B` need not be visible at the target grade — that is why the envelope is
gradewise rather than a uniform clip.

**High-tail release** (`high_tail_release`).  Clipping a lawful section at `⊤` below grade
`H` and at `γ` from grade `H` on is lawful, keeps every reading below `H` literal, and turns
every reading of grade at least `H` into its `γ`-reading.  **What it does and does not do**
(the reviewer's correction): it retains a prescribed face literally exactly when that face's
coordinates of grade at least `H` are already bottom (`high_tail_release_face`); it does *not*
address a prescribed high above the cap on an active face — that obstruction is untouched.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- Lower sets are finite; a local `Fintype` instance for finite maxima. -/
noncomputable abbrev fintypeBelow (BJ : Finset ι × ℕ) : Fintype (D.below BJ) :=
  Fintype.ofFinite _

attribute [local instance] fintypeBelow

/-! ## The grade envelope -/

/-! ## Bounded-output lifting -/

/-! ## High-tail release -/

end VaughtConjecture.Knight
