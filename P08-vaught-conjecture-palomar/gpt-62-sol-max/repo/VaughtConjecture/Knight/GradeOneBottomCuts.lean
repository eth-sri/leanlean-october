/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneExecutable
public import VaughtConjecture.Knight.GradeOneSectionLifting

/-! # Bottom patterns are source cuts

For a fixed full row, every source-monotone labelling has an initial-segment
bottom set. Thus at most n+1 cuts replace the 2^n Boolean bottom patterns in
the exact grade-one query. All nested block implications are still checked.
This is an equivalence, not heuristic pruning or a new consistency theorem.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace BottomCut

variable {Y X S L : Type*} [LinearOrder S] [LinearOrder L] [OrderBot L]

variable [Fintype X] [Fintype Y] [OrderBot S]

end BottomCut

section Semantic

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

noncomputable local instance : Fintype (D.below BJ) := Fintype.ofFinite _

end Semantic

namespace Executable.Data

variable {X Y C : Type*} [Fintype X] [Fintype Y] [Fintype C] [DecidableEq Y]

end Executable.Data

end VaughtConjecture.Knight.FullRowLifting
