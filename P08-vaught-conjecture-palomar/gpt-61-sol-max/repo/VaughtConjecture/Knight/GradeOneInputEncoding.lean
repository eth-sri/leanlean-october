/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Sort
public import VaughtConjecture.Knight.GradeOneBottomLift

/-! # Finite ordered encoding of grade-one inputs

A finite inventory of self-visible grade-one values, including arbitrary
ordinals and literal top, can be encoded by bottom and bounded positive natural
ordinals. Explicit monotone, bottom-reflecting maps encode and decode the
inventory exactly. They commute with visibility replacement up to grade one.

Both maps preserve actual respect on grade-one lower domains, with rows fixed.
This uses source-block witness repair, not transitivity of faithful transforms.
The inverse is required only on the input inventory, not on all possible
outputs. That is enough to preserve lift existence in both directions.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting

open AmalgamationPlan Transform Value ExtOrd SharpWitnessComposition

/-- A finite ordinal alphabet. Ordinal zero is omitted: it is not self-visible
at grade one. Bottom is different from ordinal zero. -/
def InAlphabet (N : ℕ) (x : ExtOrd) : Prop :=
  x = ⊥ ∨ ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ x = ofOrd n

theorem InAlphabet.visible {N : ℕ} {x : ExtOrd} (h : InAlphabet N x) : SelfVis 1 x := by
  rcases h with rfl | ⟨n, hn, _, rfl⟩
  · exact selfVis_bot 1
  · rwa [selfVis_ofOrd_iff, finitePart_natCast]

namespace InputEncoding

end InputEncoding

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ}

end VaughtConjecture.Knight.FullRowLifting
