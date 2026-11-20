/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneBottomCuts

/-! # A structural criterion for all grade-one face lifts

With common full-row orders on the face and target, unrestricted lifting
is equivalent to source-order trace and extension of admissible bottom cuts.
Both conditions concern the source rows only: no section, lawful completion,
ambient, or output-label search is hidden in the structural criterion.

Unique full controllers supply common order. All actual nested block laws,
bottom sources, and distinct occurrences are retained. This is grade one
only, and is not a native identification of KVC's semantics.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace BottomCut

variable {Y S : Type*} [LinearOrder S]

end BottomCut

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ CI : Finset ι × ℕ}

noncomputable local instance (J : Finset ι × ℕ) : Fintype (D.below J) := Fintype.ofFinite _

namespace BottomCut

end BottomCut

end VaughtConjecture.Knight.FullRowLifting
