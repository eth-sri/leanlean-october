/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneInputEncoding

/-! # A bounded universal test for a grade-one bountifulness clause

For a face with m occurrences and a target with n occurrences, all ordinal
inputs reduce to the alphabet {bottom, 1, ..., m+n+1}. Input lawfulness, cap
agreement, and the existence or nonexistence of a lift survive the reduction.

For consistent semantics and inhabited grade-one face and target indices,
lawfulness and lifting are then replaced by finite source-order and block-bottom
tests. Source rows and all occurrences remain literal. This proves a finite
universal characterization; it does not run an exhaustive solver on KVC's rows
or assert that any new construction passes. No mixed-grade claim is made.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace InputEncoding

section Inventory

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Inventory

end InputEncoding

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {CI BJ : Finset ι × ℕ}

noncomputable local instance (J : Finset ι × ℕ) : Fintype (D.below J) := Fintype.ofFinite _

end VaughtConjecture.Knight.FullRowLifting
