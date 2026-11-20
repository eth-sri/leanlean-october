/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoPointSlots

/-! # Literal two-point faces of the next three-point boundary

The nine occurrences are three singletons, two controllers on each of the
faces `{0,1}` and `{1,2}`, and one mute cell on each face. Both faces are the
actual complete bountiful two-point domain, not a single source profile.

This module supplies simultaneous proper-face sections and original-cap
retuning, retaining every controller occurrence. Full-scope rows and a legal
three-point extension are not supplied by this boundary predicate.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.ThreePointSlotBoundary

open Transform Value ExtOrd

def left : Fin 5 → Fin 9 := ![0, 1, 3, 4, 7]
def right : Fin 5 → Fin 9 := ![1, 2, 5, 6, 8]

def Lawful (p : Fin 9 → ExtOrd) : Prop :=
  RespectsSemantics TwoPointSlots.rows (p ∘ left) ∧
  RespectsSemantics TwoPointSlots.rows (p ∘ right)

end VaughtConjecture.Knight.ThreePointSlotBoundary
