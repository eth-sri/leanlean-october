/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Pruned.SliceFacts

/-!
# The pruned recursion: what one round does to the memory (Section 2.4.2, steps (2) to (4))

A call of pruned with n + 1 ≥ 1 levels left runs ten rounds, one for each term λ of Schönhage's
identity.  This file has no program in it.  It says what the memory looks like before round t
(`PrunedInv`) and shows that after the four calls of a round `PrunedInv` holds for t + 1.

* Step (3).  If the list of the child is empty, the round is over (`PrunedInv.next_of_nil`).  If
  not, what the recursive call assumes holds (`PrunedPre.child`); its arguments are `x.child n t`.
* Step (4).  What the two calls of pick assume holds (`Returned.pickFirst`, `Restricted.pickLast`),
  and afterwards `PrunedInv` holds for t + 1 (`Restricted.next`).

The memories after the calls are μ₁ (`Merged`), μ₂ (`Returned`), μ₃ (`Restricted`) and μ₄.  Each of
these records says which cells its call may have changed, and `RoundSizes` holds the inequalities
between the places of a round; that a list is still where it was follows from these two.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp.Spec

variable {lim : Limits} {n t : ℕ} {x : PrunedArgs} {μ μ' : ℕ → ℤ}

/-! ## Sizes -/

/-! ## From one round to the next -/

/-! ## The four calls of a round -/

/-- The arguments of the recursive call for the term t.  Its list is the list of the child, which
stands behind the codes in the frame; its output are the cells behind that list; its stack is what
follows. -/
@[simp]
def PrunedArgs.child (x : PrunedArgs) (n t : ℕ) : PrunedArgs :=
  { x with
    base := x.base + t * 10 ^ n
    l := x.sp + 11 + x.codes.length
    out := x.sp + 11 + 2 * x.codes.length
    sp := x.sp + 11 + 3 * x.codes.length
    codes := childList n t x.codes }

/-- The values of the child t. -/
abbrev PrunedArgs.childValues (x : PrunedArgs) (n t : ℕ) : List ℤ :=
  (childList n t x.codes).map (prunedValue x.EA x.EB n (x.base + t * 10 ^ n))

/-- The arguments of a call of pick in round t: the values of the child t are restricted to the list
small, which stands at the position pos among the codes in the frame, and go to the same position of
the output. -/
@[simp]
def PrunedArgs.pick (x : PrunedArgs) (n t pos : ℕ) (small : List ℕ) : PickArgs where
  pSub := x.sp + 11 + pos
  pU := x.sp + 11 + x.codes.length
  pVal := x.sp + 11 + 2 * x.codes.length
  pDst := x.out + pos
  small := small
  big := childList n t x.codes
  values := x.childValues n t

section Round

variable {μ₁ μ₂ μ₃ μ₄ : ℕ → ℤ} (pre : PrunedPre lim μ (n + 1) x)
  (ht : t < 10)
include pre ht

end Round

/-! ## The values -/

end Light.Sec2
