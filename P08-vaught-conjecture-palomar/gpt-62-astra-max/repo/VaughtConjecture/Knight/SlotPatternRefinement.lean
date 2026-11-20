/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceBlockPadding
public import VaughtConjecture.Knight.FiniteProfileControllers

/-! # Refining the proper boundary across a source cut

Below the cut retain the ambient source order, including distinctions erased
by its decoder. Above it use the prescribed order. The two slot cones are
closed under this operation when lower prescribed values precede upper ones.
-/

@[expose] public section

namespace VaughtConjecture.Knight.SlotPatternRefinement

def mix {X : Type*} (q b : X → ℕ) (a : ℕ) (d : X) : ℕ :=
  if q d < a then q d else a + b d

end VaughtConjecture.Knight.SlotPatternRefinement
