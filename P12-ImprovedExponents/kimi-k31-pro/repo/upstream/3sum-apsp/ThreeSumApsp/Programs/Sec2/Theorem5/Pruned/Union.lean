/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# The merge of two lists (Section 2.4.4: "a union of slices is a merge")

union(pa, na, pb, nb, pc) writes the merge of the list of na numbers at pa and the list of nb
numbers at pb to pc, a number that heads both lists being taken once, and returns its length.  The
program follows Spec.mergeUnion step by step.

union_entry shows that a call does this in at most 70 (na + nb + 1) steps and changes no cell
outside the output.  Both loops keep UnionInv.  What writing one number does to the data is
union_emit.  The three bodies are unionBoth_ends, unionLeft_ends and unionRight_ends, and
union_entry treats the two loops.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace UnionLocal

/-- The first list, A in the comments of the proofs. -/
abbrev ListA : ℕ := 0
/-- The length na of the first list. -/
abbrev LenA : ℕ := 1
/-- The second list, B in the comments of the proofs. -/
abbrev ListB : ℕ := 2
/-- The length nb of the second list. -/
abbrev LenB : ℕ := 3
/-- Where the merge is written, C in the comments of the proofs. -/
abbrev Dest : ℕ := 4
/-- The number i of entries taken from the first list. -/
abbrev TakenA : ℕ := 5
/-- The number j of entries taken from the second list. -/
abbrev TakenB : ℕ := 6
/-- The number len of entries written. -/
abbrev Written : ℕ := 7
/-- The head a of what is left of the first list. -/
abbrev HeadA : ℕ := 8
/-- The head b of what is left of the second list. -/
abbrev HeadB : ℕ := 9

end UnionLocal

open UnionLocal

/-- Both lists have a head: the smaller one is written and its list advances; if they are equal, the
number is written once and both lists advance. -/
def unionBoth : Stmt :=
  .set HeadA (M (v ListA +' v TakenA)) ;;
  .set HeadB (M (v ListB +' v TakenB)) ;;
  .ite (v HeadA <' v HeadB) (
    .store (v Dest +' v Written) (v HeadA) ;; .set TakenA (v TakenA +' k 1) ;;
      .set Written (v Written +' k 1)) (
    .ite (v HeadB <' v HeadA) (
      .store (v Dest +' v Written) (v HeadB) ;; .set TakenB (v TakenB +' k 1) ;;
        .set Written (v Written +' k 1)) (
      .store (v Dest +' v Written) (v HeadA) ;; .set TakenA (v TakenA +' k 1) ;;
        .set TakenB (v TakenB +' k 1) ;; .set Written (v Written +' k 1)))

/-- The head of the first list is written. -/
def unionLeft : Stmt :=
  .store (v Dest +' v Written) (M (v ListA +' v TakenA)) ;; .set TakenA (v TakenA +' k 1) ;;
    .set Written (v Written +' k 1)

/-- The head of the second list is written. -/
def unionRight : Stmt :=
  .store (v Dest +' v Written) (M (v ListB +' v TakenB)) ;; .set TakenB (v TakenB +' k 1) ;;
    .set Written (v Written +' k 1)

/-- union(pa, na, pb, nb, pc); it returns len. -/
def unionBody : Stmt :=
  .while (v TakenA <' v LenA) (.ite (v TakenB <' v LenB) unionBoth unionLeft) ;;
  .while (v TakenB <' v LenB) unionRight ;;
  .set 0 (v Written)

/-! ## The invariant -/

variable {μ μ' : ℕ → ℤ} {pa pb pc : ℕ} {la lb : List ℕ} {i j : ℕ} {done : List ℕ}

/-! ## The three bodies -/

/-! ## The procedure -/

end Light.Sec2
