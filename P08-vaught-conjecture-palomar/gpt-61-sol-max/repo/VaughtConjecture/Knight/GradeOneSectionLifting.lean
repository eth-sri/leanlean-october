/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneFiniteBountiful

/-! # Grade-one sections give capped lifts under a common full-row order

A lawful section and a lawful ambient that follow the same full-row source
order can be joined by the finite least-order closure. Positive cap agreement
retains the ambient's bottom pattern, so the existing locality-repair theorem
proves respect without assuming composition of faithful transformations.

In particular, a unique full controller makes the common-order condition
automatic. At such a grade-one target, arbitrary sections are equivalent to
unrestricted capped lifting. Every target occurrence is retained, and neither
the external cap nor any prescribed label is changed. Bottom uses the supplied
section itself. This does not identify a KVC scheme or apply to mixed grades.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace Propagation

section Order

variable {X Y S L : Type*} [Fintype X] [Fintype Y]
  [LinearOrder S] [OrderBot S] [LinearOrder L] [OrderBot L]

end Order

end Propagation

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ CI : Finset ι × ℕ}

noncomputable local instance (J : Finset ι × ℕ) : Fintype (D.below J) := Fintype.ofFinite _

end VaughtConjecture.Knight.FullRowLifting
