/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts
import Mathlib.Data.List.Iterate

/-!
# A query, once the digits of its output string are known

Proof of Theorem 30, "Query"; these are steps (2) and (3) of the query in Section 4.3. The routine
adds up the sum of Lemma 28: for each leaf of order below t contributing to the output string the
product of its two numbers in the encodings of the tile (queryLowRound), and for each box of the
output string its value (queryBoxRound): "we look up its value in the trie of the tile". The root of
this trie is an argument of the routine.

Leaves and boxes are enumerated through the strings of m digits with a bounded number of nines. For
the boxes the proof of Theorem 30 says "for every V ⊆ Q with |V| = m - t and every box of 𝓑_V". The
routine has one loop (queryBoxes), over the strings with exactly m - t nines: such a string gives V
(the places of its nines) and the box of 𝓑_V (its other digits) at once. This is the other way in
which Section 4.2 describes the boxes of w, "in terms of the leaves of order exactly t contributing
to w. For such a leaf, consider the lowest level of Q at which it chooses a term other than P₀, and
replace its P₀ by a star at every lower level of Q (or at every level of Q, if t = 0). The result is
a box of w, and each box of w arises exactly once in this way" (for cubes:
`existsUnique_starBelow_eq`). The members of the list of the routine are exactly the strings of the
cubes so obtained (`mem_boxesOf_iff`), and a sum over the list is the sum over the sets 𝓑_V
(`sum_boxesOf`). The sets V come interleaved, in the lexicographic order of the strings.

Both loops have one invariant, Query.Inv: the sum of the first terms stands in a local, and the
current string of the enumeration in the scratch area ss. Query.low_term and Query.box_term say
which term a round adds; Query.lowRound and Query.boxRound are the two rounds, Query.loop is either
loop, and queryCore_spec puts the two loops together.
-/


open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/

namespace Query

/- The local variables of queryCore: the arguments aA, aB, tr, root, wd, ss, box, L, m, t; the sum
so far, whether there is a further string, the code of the leaf (the result of scatter, which is not
used, goes there too), the value of the box, and m - t. -/
slots EncA EncB Tries Root Digits Str Box Levels Inner Switch Sum More Code Value Nines

end Query

open Query in
/-- One round of the first loop: a leaf of order below t. -/
def queryLowRound : Stmt :=
  .call Proc.scatter [v Digits, v Str, v Box, v Levels, k 0] Code ;;
  .call Proc.horner [v Box, v Levels] Code ;;
  .set Sum (v Sum +' M (v EncA +' v Code) *' M (v EncB +' v Code)) ;;
  .call Proc.nineNext [v Str, v Inner, v Nines +' k 1, v Inner] More

open Query in
/-- One round of the second loop: a box, looked up in the trie of the tile. -/
def queryBoxRound : Stmt :=
  .call Proc.scatter [v Digits, v Str, v Box, v Levels, k 1] Code ;;
  .call Proc.lookup [v Tries, v Root, v Box, v Levels] Value ;;
  .set Sum (v Sum +' v Value) ;;
  .call Proc.nineNext [v Str, v Inner, v Nines, v Nines] More

open Query in
/-- The leaves of order below t: the strings with more than m - t nines. -/
def queryLow : Stmt :=
  .call Proc.nineFirst [v Str, v Inner, v Nines +' k 1] More ;;
  .set More (k 1) ;;
  .while (v More =' k 1) queryLowRound

open Query in
/-- The boxes: the strings with exactly m - t nines. -/
def queryBoxes : Stmt :=
  .call Proc.nineFirst [v Str, v Inner, v Nines] More ;;
  .set More (k 1) ;;
  .while (v More =' k 1) queryBoxRound

open Query in
/-- queryCore(aA, aB, tr, root, wd, ss, box, L, m, t) returns the sum of Lemma 28. The sum starts
at 0, as all locals that are not arguments; the result of a procedure is its local 0, so the last
statement puts the sum there. -/
def queryCoreBody : Stmt :=
  .set Nines (v Inner -' v Switch) ;;
  .ite (v Switch =' k 0) .skip queryLow ;;
  queryBoxes ;;
  .set EncA (v Sum)

namespace Query

/-! ## The pure side: the terms of the sum -/

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : QueryCoreArgs} {i : ℕ}

/-- The number of leaves of order below t. -/
abbrev lowCount (x : QueryCoreArgs) : ℕ := (nineStrs x.m (x.m - x.t + 1) x.m).length

/-- The number of boxes. -/
abbrev boxCount (x : QueryCoreArgs) : ℕ := (nineStrs x.m (x.m - x.t) (x.m - x.t)).length

/-- The output string has one digit for each level. -/
theorem length_digits (x : QueryCoreArgs) : (digitsO x.η).length = x.L := length_digitsO x.η


/-- The string that round i of the first loop writes at box: a leaf of order below t. -/
def leafAt (x : QueryCoreArgs) (i : ℕ) : List ℕ :=
  scatter (digitsO x.η) (nineStr x.m (x.m - x.t + 1) x.m i)

/-- The string that round i of the second loop writes at box: a box of the output string. -/
def boxAt (x : QueryCoreArgs) (i : ℕ) : List ℕ :=
  scatter (digitsO x.η) (starRunIf true (nineStr x.m (x.m - x.t) (x.m - x.t) i))


/-- Round i of the second loop treats a box and adds its value, looked up in the trie of the
tile. -/
theorem box_term (hi : i < boxCount x) :
    boxAt x i ∈ boxesOf x.m x.t (digitsO x.η) ∧
      (x.terms.take (lowCount x + (i + 1))).sum = (x.terms.take (lowCount x + i)).sum +
        trieLookup x.T x.root (boxAt x i) := by
  have hlows : ((lowList x.m x.t (digitsO x.η)).map
      (leafProduct (arrT x.encA) (arrT x.encB))).length = lowCount x := by simp [lowList]
  have hlen : i < (boxesOf x.m x.t (digitsO x.η)).length := by grind [boxesOf]
  have hmember : (boxesOf x.m x.t _)[i] = boxAt x i := by
    refine Option.some.inj ((List.getElem?_eq_getElem hlen).symm.trans ?_)
    rw [boxesOf, List.getElem?_map, List.getElem?_eq_getElem hi, getElem_nineStrs]
    rfl
  grind [Nat.add_assoc, List.sum_take_succ_getD, QueryCoreArgs.terms, queryTerms, List.getD_append_add, List.getD_eq_getElem]

/-! ## The memory and the invariant -/

section Same

variable {μ₁ μ₂ : ℕ → ℤ} {ss m box L a : ℕ} {l : List ℤ}

/-- A write to the string at ss stays within the two scratch strings. -/
theorem same_of_ss (h : SameOutside2 μ μ₁ ss m box L) (h' : SameOutside μ₁ μ₂ ss m) :
    SameOutside2 μ μ₂ ss m box L := h.then h' fun _ hb => by omega

/-- A write to the string at box stays within the two scratch strings. -/
theorem same_of_box (h : SameOutside2 μ μ₁ ss m box L) (h' : SameOutside μ₁ μ₂ box L) :
    SameOutside2 μ μ₂ ss m box L := h.then h' fun _ hb => by omega

/-- A segment that meets neither scratch string is kept. -/
theorem seg_of_same (h : SameOutside2 μ μ₁ ss m box L) (hl : Seg μ a l)
    (h1 : Apart ss m a l.length) (h2 : Apart box L a l.length) : Seg μ₁ a l :=
  hl.of_sameOn h fun i hi => by omega

end Same

/-- The specifications of the routines that queryCore calls. -/
structure Callees (lim : Limits) (P : Program) : Prop where
  nineFirst : NineFirstSpec lim P
  nineNext : NineNextSpec lim P
  scatter : ScatterSpec lim P
  horner : HornerSpec lim P
  lookup : LookupSpec lim P

/-- The state before round i of the loop over the strings with lo to hi nines, when base terms have
been added before the loop: the sum of the first base + i terms stands in the local Sum, the local
More says whether there is a string number i, and this string stands at ss. -/
def Inv (μ : ℕ → ℤ) (x : QueryCoreArgs) (lo hi base i : ℕ) (σ : State) : Prop :=
  ∃ (code value : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.aA, x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L, x.m, x.t,
      (x.terms.take (base + i)).sum, if i < (nineStrs x.m lo hi).length then 1 else 0, code, value,
      (x.m - x.t : ℕ)], μ'⟩ ∧
    SegN μ' x.ss (nineStr x.m lo hi i) ∧ SameOutside2 μ μ' x.ss x.m x.box x.L

variable {σ : State}


/-! ## The two calls that both rounds make -/

section Calls

variable {lo hi : ℕ} {μ₀ : ℕ → ℤ}



end Calls

/-! ## The two rounds -/



/-! ## The two loops -/


/-- The state between the loops: the sum of the first n terms stands in the local Sum. -/
def Mid (μ : ℕ → ℤ) (x : QueryCoreArgs) (n : ℕ) (σ : State) : Prop :=
  ∃ (more code value : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.aA, x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L, x.m, x.t, (x.terms.take n).sum,
      more, code, value, (x.m - x.t : ℕ)], μ'⟩ ∧ SameOutside2 μ μ' x.ss x.m x.box x.L

/-- After a loop, only the sum and the memory matter. -/
theorem Inv.mid {lo hi base : ℕ} (h : Inv μ x lo hi base i σ) : Mid μ x (base + i) σ := by
  obtain ⟨code, value, μ', rfl, -, same⟩ := h
  exact ⟨_, code, value, μ', rfl, same⟩




end Query

