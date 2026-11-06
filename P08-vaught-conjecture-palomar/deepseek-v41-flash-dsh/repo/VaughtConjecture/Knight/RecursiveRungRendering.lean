/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RungTableRendering
public import VaughtConjecture.Knight.CanonicalFieldLayer

/-! # Recursive raw rows and rendered prefixes over the long rung base

Stage `n` retains the entire rung base and the leaf catalogues of grades
2 through `n + 1`. The catalogue and every occurrence are fixed before an
input is rendered. Raw rows use the previous renderer at the new native grid;
rendered vectors apply one outer paired-slot decoder to the normalized row.

The prefix theorem is proved by grade induction, not carried as a field of
an invariant. Support follows from the outer decoder. The exact base formula
includes every unused rung and follows from whole-table decoding.

These are numerical master vectors, including complete original fields. No
admission, geometric installation, consistency, or bountifulness is asserted.
In particular, retaining the occurrence type does not assert equality of
independently selected renderings at different construction grades.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.RecursiveRungRendering
open Transform Value ExtOrd SourcePrefixRows
open PairedSlotEncoding PairedSlotComparison
noncomputable section

universe u v
variable {X : Type u} {B : Type v} [Fintype X] {Q : ℕ → Type v}




abbrev grid (X : Type*) [Fintype X] (j : ℕ) := sourceGrid j (Fintype.card X)
abbrev ceiling (X : Type*) [Fintype X] (j : ℕ) := CanonicalFieldLayer.ceiling j X


variable (ranks : B → X → ℕ) (fields : (j : ℕ) → Q j → X → ExtOrd)





end
end VaughtConjecture.Knight.RecursiveRungRendering
