/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeOneBottomCuts

/-! # Appending a source above the inherited inventory

Inherited cuts extend with the new occurrence nonbottom. If the new owner's
old block triples copy a source-maximal donor, their bottom implications add
no restriction on those cuts. The new all-bottom cut is also permitted.

The block table is an explicit hypothesis, not a constructed row or scheme.
This proves bottom-pattern preservation only: source witnesses, geometry,
availability, prescribed labels, and successor closure are not supplied.
-/

@[expose] public section

namespace VaughtConjecture.Knight.FullRowLifting.BottomCut

variable {Y S : Type*} [LinearOrder S]

/-- Nested block implications, written directly on the bottom flags. -/
def Closed (B : Y → Y → Y → Prop) (z : Y → Bool) : Prop :=
  ∀ c d e, B c d e → (z d = true ∨ z c = true) → (z e = true ∨ z c = true)

instance [Fintype Y] (B : Y → Y → Y → Prop) [∀ c d e, Decidable (B c d e)]
    (z : Y → Bool) : Decidable (Closed B z) :=
  inferInstanceAs (Decidable (∀ c d e, B c d e →
    (z d = true ∨ z c = true) → (z e = true ∨ z c = true)))

/-- Retain all old triples, copy a donor's old triples to the new owner,
and give the fresh occurrence its own block. No cross-block triple is added. -/
def donorBlocks (B : Y → Y → Y → Prop) (t : Y) :
    Option Y → Option Y → Option Y → Prop
  | some c, some d, some e => B c d e
  | none, some d, some e => B t d e
  | none, none, none => True
  | _, _, _ => False

instance (B : Y → Y → Y → Prop) [∀ c d e, Decidable (B c d e)]
    (t : Y) (c d e : Option Y) : Decidable (donorBlocks B t c d e) := by
  cases c <;> cases d <;> cases e <;> unfold donorBlocks <;> infer_instance

end VaughtConjecture.Knight.FullRowLifting.BottomCut
