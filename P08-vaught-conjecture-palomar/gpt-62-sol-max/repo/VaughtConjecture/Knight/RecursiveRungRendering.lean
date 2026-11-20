/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RungTableRendering
public import VaughtConjecture.Knight.CanonicalFieldLayer

@[expose] public section

namespace VaughtConjecture.Knight.RecursiveRungRendering

open Transform Value ExtOrd SourcePrefixRows

open PairedSlotEncoding PairedSlotComparison

noncomputable section

universe u v

variable {X : Type u} [Fintype X]

abbrev ceiling (X : Type*) [Fintype X] (j : ℕ) := CanonicalFieldLayer.ceiling j X

end

end VaughtConjecture.Knight.RecursiveRungRendering
