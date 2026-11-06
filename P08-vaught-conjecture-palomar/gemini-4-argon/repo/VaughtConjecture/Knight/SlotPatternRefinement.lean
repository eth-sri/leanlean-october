/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoPointSlotPatterns

/-! # Refining the proper boundary across a source cut

Below the cut retain the ambient source order, including distinctions erased
by its decoder. Above it use the prescribed order. The two slot cones are
closed under this operation when lower prescribed values precede upper ones.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.SlotPatternRefinement

open Transform Value ExtOrd SlotControllerFamily ThreePointSlotBoundary

def mix {X : Type*} (q b : X → ℕ) (a : ℕ) (d : X) : ℕ :=
  if q d < a then q d else a + b d

end VaughtConjecture.Knight.SlotPatternRefinement
