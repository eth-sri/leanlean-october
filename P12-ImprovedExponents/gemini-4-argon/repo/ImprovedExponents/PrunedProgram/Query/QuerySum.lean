module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts
public import Mathlib.Data.List.Iterate
public import ImprovedExponents.PrunedProgram.SegOn

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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

/-- The local variables of queryCore: the arguments aA, aB, tr, root, wd, ss, box, L, m, t; the sum
so far, whether there is a further string, the code of the leaf (the result of scatter, which is not
used, goes there too), the value of the box, and m - t. -/
abbrev EncA : ℕ := 0
@[inherit_doc EncA] abbrev EncB : ℕ := 1
@[inherit_doc EncA] abbrev Tries : ℕ := 2
@[inherit_doc EncA] abbrev Root : ℕ := 3
@[inherit_doc EncA] abbrev Digits : ℕ := 4
@[inherit_doc EncA] abbrev Str : ℕ := 5
@[inherit_doc EncA] abbrev Box : ℕ := 6
@[inherit_doc EncA] abbrev Levels : ℕ := 7
@[inherit_doc EncA] abbrev Inner : ℕ := 8
@[inherit_doc EncA] abbrev Switch : ℕ := 9
@[inherit_doc EncA] abbrev Sum : ℕ := 10
@[inherit_doc EncA] abbrev More : ℕ := 11
@[inherit_doc EncA] abbrev Code : ℕ := 12
@[inherit_doc EncA] abbrev Value : ℕ := 13
@[inherit_doc EncA] abbrev Nines : ℕ := 14

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
  refine ⟨List.mem_map.mpr ⟨_, nineStr_mem hi, rfl⟩, ?_⟩
  have hlows : ((lowList x.m x.t (digitsO x.η)).map
      (leafProduct (arrT x.encA) (arrT x.encB))).length = lowCount x := by simp [lowList]
  have hlen : i < (boxesOf x.m x.t (digitsO x.η)).length := by simpa [boxesOf] using hi
  have hmember : (boxesOf x.m x.t (digitsO x.η))[i] = boxAt x i := by
    refine Option.some.inj ((List.getElem?_eq_getElem hlen).symm.trans ?_)
    rw [boxesOf, List.getElem?_map, List.getElem?_eq_getElem hi, getElem_nineStrs hi]
    rfl
  rw [← Nat.add_assoc, List.sum_take_succ_getD, QueryCoreArgs.terms, queryTerms, ← hlows,
    List.getD_append_add,
    List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getElem_map, hmember]

/-! ## The memory and the invariant -/

section Same

variable {μ₁ μ₂ : ℕ → ℤ} {ss m box L a : ℕ} {l : List ℤ}

/-- A write to the string at ss stays within the two scratch strings. -/
theorem same_of_ss (h : SameOutside2 μ μ₁ ss m box L) (h' : SameOutside μ₁ μ₂ ss m) :
    SameOutside2 μ μ₂ ss m box L := h.then h' fun _ hb => ⟨hb, hb.1⟩

/-- A write to the string at box stays within the two scratch strings. -/
theorem same_of_box (h : SameOutside2 μ μ₁ ss m box L) (h' : SameOutside μ₁ μ₂ box L) :
    SameOutside2 μ μ₂ ss m box L := h.then h' fun _ hb => ⟨hb, hb.2⟩

/-- A segment that meets neither scratch string is kept. -/
theorem seg_of_same (h : SameOutside2 μ μ₁ ss m box L) (hl : Seg μ a l)
    (h1 : Apart ss m a l.length) (h2 : Apart box L a l.length) : Seg μ₁ a l :=
  hl.of_sameOn h fun i hi => ⟨by omega, by omega⟩

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






/-!
# The specification of `queryCore` on pruned encodings

Upstream's `queryCore` (procedure 53) assumes the two encodings of the tile as full segments
(`QueryCorePre.segA/segB : Seg μ aA (arrT encA)`).  It reads them at the leaves of order below `t`
contributing to the output string only, and such a leaf has at most `m` symbols `P₀`
(`card_P0Levels_le_of_contributes`, with `QueryCorePre.card`).  `QueryCorePreP` is `QueryCorePre`
with `SegOn m` in place of `Seg` in these two fields, and `QueryCoreSpecP` is `QueryCoreSpec` with
this weaker assumption; the routine and its time are upstream's.  `QueryCorePre.toP` says that the
full assumption implies the weaker one, and `segOn_of_same` that the two scratch strings of the
routine do not disturb a pruned encoding.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean` (Apache-2.0).
-/



/-- What `queryCore` assumes when the encodings are right at the leaves with at most `m` symbols
`P₀` only: upstream's `QueryCorePre` with `SegOn x.m` in place of `Seg` for the two encodings. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean (QueryCorePre)
structure QueryCorePreP (lim : Limits) (μ : ℕ → ℤ) (x : QueryCoreArgs) : Prop where
  std : Std lim
  t_le : x.t ≤ x.m
  card : (innerSetO x.η).card = x.m
  segA : SegOn x.m μ x.aA x.encA
  segB : SegOn x.m μ x.aB x.encB
  segT : Seg μ x.tr x.T
  segDigits : SegN μ x.wd (digitsO x.η)
  walk : ∀ l ∈ boxesOf x.m x.t (digitsO x.η), WalkOK x.T x.root l
  sums : ∀ j, |(x.terms.take j).sum| ≤ lim.word
  prod : ∀ τ, |x.encA τ * x.encB τ| ≤ lim.word
  pow : (10 : ℤ) ^ x.L ≤ lim.word
  ss_wd : Apart x.ss x.m x.wd x.L
  box_wd : Apart x.box x.L x.wd x.L
  ss_box : Apart x.ss x.m x.box x.L
  ss_aA : Apart x.ss x.m x.aA (10 ^ x.L)
  ss_aB : Apart x.ss x.m x.aB (10 ^ x.L)
  box_aA : Apart x.box x.L x.aA (10 ^ x.L)
  box_aB : Apart x.box x.L x.aB (10 ^ x.L)
  ss_tr : Apart x.ss x.m x.tr x.T.length
  box_tr : Apart x.box x.L x.tr x.T.length
  aA_lt : x.aA + 10 ^ x.L < lim.space
  aB_lt : x.aB + 10 ^ x.L < lim.space
  tr_lt : x.tr + x.T.length < lim.space
  wd_lt : x.wd + x.L < lim.space
  ss_lt : x.ss + x.m < lim.space
  box_lt : x.box + x.L < lim.space

/-- `queryCore` returns the sum `trieQuery` for the output string whose digits are at wd, when the
two encodings are right at the leaves with at most `m` symbols `P₀` only; it changes only the two
scratch strings.  Same procedure number and time as upstream. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Contracts.lean (QueryCoreSpec)
def QueryCoreSpecP (lim : Limits) (P : Program) : Prop :=
  ∀ (x : QueryCoreArgs) (μ : ℕ → ℤ), QueryCorePreP lim μ x →
    ∀ d, d + 1 ≤ lim.depth →
    Meets lim P Proc.queryCore d [x.aA, x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L, x.m, x.t] μ
      (tQueryCore x.L x.m x.t) fun r μ' =>
        r = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) ∧
          SameOutside2 μ μ' x.ss x.m x.box x.L

variable {lim : Limits} {μ μ₁ : ℕ → ℤ} {x : QueryCoreArgs}

/-- A pruned encoding that meets neither scratch string is kept. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.seg_of_same)
theorem segOn_of_same {ss m box L a k L' : ℕ} {enc : Leaf L' → ℤ}
    (h : SameOutside2 μ μ₁ ss m box L) (hl : SegOn k μ a enc)
    (h1 : Apart ss m a (10 ^ L')) (h2 : Apart box L a (10 ^ L')) : SegOn k μ₁ a enc :=
  hl.congr fun i hi => h _ ⟨by omega, by omega⟩






/-!
# A query, once the digits of its output string are known, on pruned encodings

Upstream's `queryCore_spec` proves the routine `queryCoreBody` (procedure 53: the leaves of order
below `t`, then the boxes) under `QueryCorePre`, which holds the two encodings of the tile as full
segments.  The routine reads an encoding in one place only: a round of the first loop reads the
cell of the leaf τ that it treats (`Query.lowRound`, "sum := sum + aA[code] * aB[code]").  This
leaf contributes to the output string η and has order below `t` (`exists_of_mem_lowList`), so it
has the term `P₀` only at the inner levels of η (`card_P0Levels_le_of_contributes`), of which there
are `m` (`QueryCorePreP.card`): the pruned encodings hold its cell (`SegOn.get`).

`queryCoreP_spec` is `queryCore_spec` under `QueryCorePreP`, with `SegOn` in place of `Seg` for
the two encodings; the program, the time and all the other steps are upstream's.  The parts of the
proof that do not mention the precondition (`Query.lowCount`, `Query.Inv`, `Query.box_term`, …)
are reused; those that do are copied with `QueryCorePreP` in place of `QueryCorePre`, under the
same names with a `P` (`lowRoundP`, `low_specP`, …).

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean` (Apache-2.0).
-/




namespace QueryP

open Query

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : QueryCoreArgs} {i : ℕ}

/-! ## The pure side: the terms of the sum -/

/-- The digit 9, which stands at the levels of the subset, occurs m times. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.count_digits)
theorem count_digitsP (C : QueryCorePreP lim μ x) : (digitsO x.η).count 9 = x.m := by
  rw [← card_innerSetO, C.card]

/-- Round i of the first loop treats a leaf τ and adds the product of its two numbers.  The leaf
contributes to the output string, so it has at most m symbols `P₀`: the pruned encodings hold its
cell. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.low_term)
theorem low_termP (C : QueryCorePreP lim μ x) (hi : i < lowCount x) :
    ∃ τ : Leaf x.L, leafAt x i = digitsT τ ∧ (P0Levels τ).card ≤ x.m ∧
      (x.terms.take (i + 1)).sum = (x.terms.take i).sum + x.encA τ * x.encB τ := by
  have hleaf : leafAt x i ∈ lowList x.m x.t (digitsO x.η) :=
    List.mem_map.mpr ⟨_, nineStr_mem hi, rfl⟩
  obtain ⟨τ, hlow, hτ⟩ := exists_of_mem_lowList C.card _ hleaf
  refine ⟨τ, hτ.symm, ?_, ?_⟩
  · -- the leaf contributes to η, which has m inner levels
    simp only [lowLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hlow
    rw [← C.card]
    exact card_P0Levels_le_of_contributes hlow.1
  have hlen : i < (lowList x.m x.t (digitsO x.η)).length := by simpa [lowList] using hi
  have hmember : (lowList x.m x.t (digitsO x.η))[i] = digitsT τ := by
    rw [hτ]
    refine Option.some.inj ((List.getElem?_eq_getElem hlen).symm.trans ?_)
    rw [lowList, List.getElem?_map, List.getElem?_eq_getElem hi, getElem_nineStrs hi]
    rfl
  rw [List.sum_take_succ_getD, QueryCoreArgs.terms, queryTerms,
    List.getD_append _ _ _ _ (by rwa [List.length_map]),
    List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getElem_map, hmember,
    leafProduct_digitsT]

/-! ## The memory and the invariant -/

variable {σ : State}

/-- The digits of the output string are kept. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.segDigits)
theorem segDigitsP (C : QueryCorePreP lim μ x) {μ' : ℕ → ℤ}
    (same : SameOutside2 μ μ' x.ss x.m x.box x.L) :
    SegN μ' x.wd (digitsO x.η) :=
  seg_of_same same C.segDigits (by simpa [length_digits] using C.ss_wd)
    (by simpa [length_digits] using C.box_wd)

/-! ## The two calls that both rounds make -/

section Calls

variable {lo hi : ℕ} {μ₀ : ℕ → ℤ}

/-- scatter(wd, ss, box, L, star) writes the leaf or the box of string number i at box; the string
at ss is kept. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.scatter_meets)
theorem scatter_meetsP (K : Callees lim P) (C : QueryCorePreP lim μ x) (star : Bool)
    (hstr : i < (nineStrs x.m lo hi).length) (hss : SegN μ₀ x.ss (nineStr x.m lo hi i))
    (same : SameOutside2 μ μ₀ x.ss x.m x.box x.L) (hd : d ≤ lim.depth) :
    Meets lim P Proc.scatter d [x.wd, x.ss, x.box, x.L, if star then 1 else 0] μ₀ (tScatter x.L)
      fun _ μ₁ => SegN μ₁ x.box (scatter (digitsO x.η) (starRunIf star (nineStr x.m lo hi i))) ∧
        SegN μ₁ x.ss (nineStr x.m lo hi i) ∧ SameOutside2 μ μ₁ x.ss x.m x.box x.L := by
  obtain ⟨hlen, -⟩ := (mem_nineStrs _).mp (nineStr_mem hstr)
  have := C.ss_box
  refine (K.scatter x.wd x.ss x.box x.L star (digitsO x.η) _ μ₀ (segDigitsP C same) hss
    (length_digits x) (by rw [hlen, count_digitsP C]) C.box_wd
    (by omega) C.wd_lt (by rw [hlen]; exact C.ss_lt) C.box_lt _
      (by omega)).mono le_rfl fun _ μ₁ ⟨hbox, same₁⟩ => ⟨hbox, ?_, same_of_box same same₁⟩
  exact hss.of_sameOutside same₁ (by omega)

/-- nineNext(ss, m, lo, hi) goes on to string number i + 1 and says whether there is one. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.next_meets)
theorem next_meetsP (K : Callees lim P) (C : QueryCorePreP lim μ x)
    (hstr : i < (nineStrs x.m lo hi).length) (hss : SegN μ₀ x.ss (nineStr x.m lo hi i))
    (same : SameOutside2 μ μ₀ x.ss x.m x.box x.L) (hd : d ≤ lim.depth) :
    Meets lim P Proc.nineNext d [x.ss, x.m, lo, hi] μ₀ (tNineNext x.m) fun r μ₁ =>
      r = (if i + 1 < (nineStrs x.m lo hi).length then 1 else 0) ∧
        SegN μ₁ x.ss (nineStr x.m lo hi (i + 1)) ∧ SameOutside2 μ μ₁ x.ss x.m x.box x.L := by
  refine (K.nineNext x.ss x.m lo hi _ μ₀ hss (nineStr_mem hstr) C.ss_lt _ (by omega)).mono le_rfl
    fun r μ₁ ⟨hss₁, hr, same₁⟩ => ⟨?_, nineStr_succ .. ▸ hss₁, same_of_ss same same₁⟩
  rw [hr, isSome_nineNext_nineStr hstr]
  simp

end Calls

/-! ## The two rounds -/

/-- One round of the first loop adds the term of the leaf number i.  The one change to upstream's
proof: the two cells read are those of a leaf with at most m symbols `P₀`, which the pruned
encodings hold (`SegOn.get`). -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.lowRound)
theorem lowRoundP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (hi : i < lowCount x) (h : Inv μ x (x.m - x.t + 1) x.m 0 i σ) :
    Ends lim P d queryLowRound σ (tScatter x.L + tHorner x.L + tNineNext x.m + 31)
      (Inv μ x (x.m - x.t + 1) x.m 0 (i + 1)) := by
  obtain ⟨code, value, μ₀, rfl, hss, same⟩ := h
  light_facts C C.std
  obtain ⟨τ, hτ, hfew, hsum⟩ := low_termP C hi
  -- code := scatter(wd, ss, box, L, 0): the leaf
  light_call (scatter_meetsP K C false hi hss same (by omega)) with _ μ₁ ⟨hbox, hss₁, same₁⟩
  replace hbox : SegN μ₁ x.box (digitsT τ) := hτ ▸ hbox
  -- code := horner(box, L)
  light_call (K.horner x.box x.L (digitsT τ) μ₁ hbox (length_digitsT τ) (digitsT_lt τ)
    C.box_lt C.pow _ (by omega)) with _ μ' ⟨rfl, hμ'⟩
  obtain rfl : μ₁ = μ' := hμ'.symm
  rw [ofDigitList_digitsT]
  -- sum := sum + aA[code] * aB[code]: the leaf has few symbols P₀, so its cells are right
  have : codeT τ < 10 ^ x.L := codeT_lt τ
  light_facts C
  have hreadA : μ₁ (x.aA + codeT τ) = x.encA τ :=
    (segOn_of_same same₁ C.segA C.ss_aA C.box_aA).get hfew
  have hreadB : μ₁ (x.aB + codeT τ) = x.encB τ :=
    (segOn_of_same same₁ C.segB C.ss_aB C.box_aB).get hfew
  have := abs_le.1 (C.prod τ)
  have hfits := abs_le.1 (C.sums (i + 1))
  rw [hsum] at hfits
  light_set ((x.terms.take i).sum + x.encA τ * x.encB τ) using hreadA, hreadB
  -- more := nineNext(ss, m, m - t + 1, m)
  light_call (next_meetsP K C hi hss₁ same₁ (by omega)) with _ μ₂ ⟨rfl, hss₂, same₂⟩
  exact ⟨codeT τ, value, μ₂, by simp [hsum], hss₂, same₂⟩

/-- One round of the second loop adds the value of the box number i. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.boxRound)
theorem boxRoundP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (hi : i < boxCount x) (h : Inv μ x (x.m - x.t) (x.m - x.t) (lowCount x) i σ) :
    Ends lim P d queryBoxRound σ (tScatter x.L + tLookup x.L + tNineNext x.m + 31)
      (Inv μ x (x.m - x.t) (x.m - x.t) (lowCount x) (i + 1)) := by
  obtain ⟨code, value, μ₀, rfl, hss, same⟩ := h
  light_facts C.std
  -- what is known about the box
  obtain ⟨hbox, hsum⟩ := box_term hi
  obtain ⟨π, -, hπ⟩ := exists_of_mem_boxesOf C.t_le C.card _ hbox
  have hlen : (boxAt x i).length = x.L := by rw [boxAt, length_scatter, length_digits]
  -- code := scatter(wd, ss, box, L, 1): the box
  light_call (scatter_meetsP K C true hi hss same (by omega)) with void μ₁ ⟨hbox₁, hss₁, same₁⟩
  -- value := lookup(tr, root, box, L)
  light_call (K.lookup x.tr x.root x.box x.L x.T (boxAt x i) μ₁
    (seg_of_same same₁ C.segT C.ss_tr C.box_tr) hbox₁ hlen (hπ ▸ digitsC_lt π) (C.walk _ hbox)
    C.tr_lt C.box_lt _ (by omega)) with _ μ' ⟨rfl, hμ'⟩
  obtain rfl : μ₁ = μ' := hμ'.symm
  -- sum := sum + value
  have hfits := abs_le.1 (C.sums (lowCount x + (i + 1)))
  rw [hsum] at hfits
  generalize trieLookup x.T x.root (boxAt x i) = val at *
  light_set ((x.terms.take (lowCount x + i)).sum + val)
  -- more := nineNext(ss, m, m - t, m - t)
  light_call (next_meetsP K C hi hss₁ same₁ (by omega)) with _ μ₂ ⟨rfl, hss₂, same₂⟩
  exact ⟨void, val, μ₂, by simp [hsum], hss₂, same₂⟩

/-! ## The two loops -/

/-- Either loop: as long as there is a further string, one round. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.loop)
theorem loopP (C : QueryCorePreP lim μ x) {round : Stmt} {lo hi base b : ℕ}
    (hround : ∀ i σ, i < (nineStrs x.m lo hi).length → Inv μ x lo hi base i σ →
      Ends lim P d round σ (b + 31) (Inv μ x lo hi base (i + 1)))
    (h : Inv μ x lo hi base 0 σ) :
    Ends lim P d (.while (v More =' k 1) round) σ ((nineStrs x.m lo hi).length * (b + 90) + 4)
      (Inv μ x lo hi base (nineStrs x.m lo hi).length) := by
  have := C.std.const_le
  have := Nat.mul_le_mul_left (nineStrs x.m lo hi).length
    (show 1 + 1 + 1 + 1 + (b + 31) ≤ b + 90 by omega)
  refine Ends.whileConst (Inv μ x lo hi base) (nineStrs x.m lo hi).length (b + 31) h ?round ?done
    (by simp only [Cond.cost, Expr.cost]; omega)
  case round =>
    rintro i σ hi hI
    have hends := hround i σ hi hI
    obtain ⟨code, value, μ', rfl, -⟩ := hI
    exact ⟨by simp; omega, by simp [hi], hends⟩
  case done =>
    rintro σ hI
    have := hI
    obtain ⟨code, value, μ', rfl, -⟩ := this
    exact ⟨by simp; omega, by simp, hI⟩

/-- The leaves of order below t. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.low_spec)
theorem low_specP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (ht : 1 ≤ x.t) (h : Mid μ x 0 σ) :
    Ends lim P d queryLow σ
      (tNineFirst x.m + lowCount x * (tScatter x.L + tHorner x.L + tNineNext x.m + 90) + 16)
      (Mid μ x (lowCount x)) := by
  obtain ⟨more, code, value, μ₀, rfl, same⟩ := h
  have := C.t_le
  light_facts C C.std
  have hpos : 0 < lowCount x := length_nineStrs_pos (by omega) (by omega)
  -- nineFirst(ss, m, m - t + 1); more := 1
  light_call (K.nineFirst x.ss x.m (x.m - x.t + 1) μ₀ (by omega) C.ss_lt _
    (by omega)) with _ μ₁ ⟨hss, same₁⟩
  light_set 1
  -- the loop
  refine (loopP C (b := tScatter x.L + tHorner x.L + tNineNext x.m)
    (fun i σ hi hI => lowRoundP K C hd hi hI)
    ⟨code, value, μ₁, by simp [hpos], hss, same_of_ss same same₁⟩).mono (by simp [lowCount]; omega)
    fun σ' hI => ?_
  simpa using hI.mid

/-- The boxes. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.boxes_spec)
theorem boxes_specP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (h : Mid μ x (lowCount x) σ) :
    Ends lim P d queryBoxes σ
      (tNineFirst x.m + boxCount x * (tScatter x.L + tLookup x.L + tNineNext x.m + 90) + 16)
      (Mid μ x (lowCount x + boxCount x)) := by
  obtain ⟨more, code, value, μ₀, rfl, same⟩ := h
  light_facts C.std
  have hpos : 0 < boxCount x := length_nineStrs_pos (by omega) le_rfl
  -- nineFirst(ss, m, m - t); more := 1
  light_call (K.nineFirst x.ss x.m (x.m - x.t) μ₀ (by omega) C.ss_lt _ (by omega))
    with _ μ₁ ⟨hss, same₁⟩
  light_set 1
  -- the loop
  exact (loopP C (b := tScatter x.L + tLookup x.L + tNineNext x.m)
    (fun i σ hi hI => boxRoundP K C hd hi hI)
    ⟨code, value, μ₁, by simp [hpos], hss, same_of_ss same same₁⟩).mono (by simp [boxCount]; omega)
    fun σ' hI => hI.mid

/-- The boxes, and the result. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.tail_spec)
theorem tail_specP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (h : Mid μ x (lowCount x) σ) :
    Ends lim P d (queryBoxes ;; .set EncA (v Sum)) σ
      (tNineFirst x.m + boxCount x * (tScatter x.L + tLookup x.L + tNineNext x.m + 90) + 18)
      fun σ' =>
      σ'.loc 0 = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) ∧
        SameOutside2 μ σ'.mem x.ss x.m x.box x.L := by
  -- the boxes
  light_piece (boxes_specP K C hd h) with _ ⟨more, code, value, μ', rfl, same⟩
  have hlen : x.terms.length = lowCount x + boxCount x := by
    simp [QueryCoreArgs.terms, queryTerms, lowList, boxesOf]
  have hall : (x.terms.take (lowCount x + boxCount x)).sum
      = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) := by
    rw [← hlen, List.take_length, QueryCoreArgs.terms, trieQuery]
  rw [hall]
  generalize trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) = result
  -- return sum
  light_set result
  exact ⟨rfl, same⟩

end QueryP

open Query QueryP in
/-- **queryCore** meets its specification on pruned encodings: upstream's routine, under the
assumption that the two encodings are right at the leaves with at most `m` symbols `P₀` only. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (queryCore_spec)
theorem queryCoreP_spec {lim : Limits} {P : Program}
    (hP : P[Proc.queryCore]? = some queryCoreBody) (K : Callees lim P) : QueryCoreSpecP lim P := by
  intro x μ C
  refine fun d hd => ⟨queryCoreBody, hP, ?_⟩
  have := C.t_le
  light_facts C C.std
  have hlows : (lowList x.m x.t ([] : List ℕ)).length = lowCount x := by simp [lowList]
  have hboxes : (boxesOf x.m x.t ([] : List ℕ)).length = boxCount x := by simp [boxesOf]
  unfold tQueryCore
  rw [hlows, hboxes]
  -- nines := m - t
  light_set (x.m - x.t : ℕ)
  have hstart : Mid μ x 0 ⟨frame (setLocal [(x.aA : ℤ), x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L,
      x.m, x.t] Nines (x.m - x.t : ℕ)), μ⟩ := ⟨0, 0, 0, μ, by simp, .refl⟩
  -- if t = 0 there are no leaves of order below t
  light_if ht0 ht1 : x.t = 0
  · have hnone : lowCount x = 0 := by
      rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
      intro l hl
      obtain ⟨-, -, hmin, hmax⟩ := (mem_nineStrs l).mp hl
      omega
    light_piece (tail_specP K C hd (hnone ▸ hstart))
  · -- the leaves of order below t, then the boxes
    light_piece (low_specP K C hd (by omega) hstart) with σ' hmid
    light_piece (tail_specP K C hd hmid)

end Light.Sec4

