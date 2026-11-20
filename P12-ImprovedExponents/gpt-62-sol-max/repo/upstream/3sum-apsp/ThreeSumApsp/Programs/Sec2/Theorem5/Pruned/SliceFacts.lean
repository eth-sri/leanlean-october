/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Theorem5.WordSize

/-!
# The pruned recursion: the pure side

What the program for Pruned (Section 2.4.2) needs to know about its model Spec.prunedList, which
works on increasing lists of codes.  A code is an output string read as a number with the digits 0
to 9: the digits 0 to 8 stand for the variables z_ij and the digit 9 for z₀.  The slice at the digit
z is sliceList n z l, the codes of l with first digit z, without that digit.

* The value that belongs to a code does not depend on the list in which the code is passed
  (`prunedValue`, `prunedList_eq_map`).
* The lists passed to the children are increasing lists of codes again, and the lengths add up
  (`segStart_ten`).
* Step (4): the result is made of the slices of the children's results (`prunedList_succ`).
* Step (2): the list of a child is the merge of the slice at the output variable of its term
  (`firstList`, empty for the term P₀) and the slice at z₀ (`childList_eq_mergeUnion`).
* The running time `prunedTime` follows the recursion of the program; it is built from the times of
  a round (`roundTime`) and of steps (3) and (4) (`childTime`).  It is at most a constant times
  prunedWork, one unit for each call and for each code passed to a call (`prunedTime_le`).  One
  round is `roundTime_le`, and the ten rounds are added up by `sum_helper_lengths`.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

/-- The value of Pruned at the output string with code c, at the vertex whose part of the encodings
begins at position base: the sum of the products at the leaves that contribute to the string. -/
def prunedValue (EA EB : List ℤ) (n base c : ℕ) : ℤ :=
  ∑ τ : Leaf n with Leaf.Contributes τ (decodeO n c),
    EA.getD (base + codeT τ) 0 * EB.getD (base + codeT τ) 0

section Children

variable {n : ℕ} {l : List ℕ} (hl : l.Pairwise (· < ·))
include hl

end Children

/-! ## Positions of the segments -/

/-! ## The model, one level unfolded -/

/-! ## The lists of a round -/

section

variable {n t : ℕ} {codes : List ℕ}

end

/-! ## The running time -/

end Light.Sec2
