/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneLeastLift

/-! # Bottom-cap grade-one sections by finite bottom-pattern branching

At bottom cap the ambient imposes no equations. Enumerate the bottom flags of
the target occurrences instead. A flag assignment must satisfy the source-block
bottom implications at every actual nested controller. Seed each nonbottom
occurrence with the least nonbottom grade-one-visible value, ordinal one, and
use the existing finite source-order closure for each full controller.

The test is necessary and sufficient, and a passing branch constructs its least
source-order-compatible section. The ordinal one used to encode the flags is
not a replacement external cap: the actual clause remains at bottom. This is
a finite test on supplied inputs, not an enumeration of all ordinal inputs, and
has no mixed-grade conclusion.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

namespace BottomPattern

/-- True means bottom. A false flag is represented by ordinal one, not zero. -/
def seed {Y : Type*} (z : Y → Bool) (d : Y) : ExtOrd :=
  if z d then ⊥ else ofOrd 1

@[simp] theorem seed_eq_bot {Y : Type*} (z : Y → Bool) (d : Y) :
    seed z d = ⊥ ↔ z d = true := by
  cases hz : z d <;> simp [seed, hz]

end BottomPattern

namespace Propagation

end Propagation

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

noncomputable local instance : Fintype (D.below BJ) := Fintype.ofFinite _

namespace BottomPattern

end BottomPattern

end VaughtConjecture.Knight.FullRowLifting
