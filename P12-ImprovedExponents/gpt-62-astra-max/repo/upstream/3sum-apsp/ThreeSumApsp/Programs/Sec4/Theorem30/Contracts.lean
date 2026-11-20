/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Slots
public import ThreeSumApsp.Lang.Calls
public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Spec.Sec2.Theorem5.Layout
public import ThreeSumApsp.Spec.Sec4.Theorem30.QueryLists
public import ThreeSumApsp.Spec.Sec4.Theorem30.StarBoxes
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.SplitIfs

/-!
# Theorem 30 in the light language: procedure numbers, time functions, specifications

This file contains no program, and its only proof is a short remark on the trie area when other
cells change. It states the specifications of the procedures 40 to 53 (`nineFirst` to `queryCore`).
The proof of a routine uses only the specifications of the routines that it calls.

* A routine takes its scalars and the base addresses of its arrays as arguments; no routine but
  `preCore` and `queryAt` knows the memory map. The routines for a tile assume the order in which
  their areas lie (`TileCtx.layout`).
* The specification of a routine is a proposition XSpec lim P: "procedure number Proc.x of the
  program P, started on these arguments in a memory that satisfies this, ends within tX steps with
  this result in a memory that satisfies that". The file of x proves XSpec for every program P that
  holds the body of x at the number Proc.x and meets the specifications of the routines that x
  calls. A caller assumes XSpec and feeds it to the rule for calls. XSpec holds at every depth d of
  calls that leaves the levels which x needs below itself.
* Conventions of the programs: the result of a procedure is what it leaves in its local 0; locals
  that are not arguments start at 0. In the proofs, lines such as "have hw := C.std.space_le" or
  "obtain ⟨⟩ := areas p t b0" state the facts on the limits and on the map that the later steps use.
* The larger routines have two records: XArgs holds the arguments and the data behind them, and
  XPre lim μ x says what the routine assumes about the limits and the memory.
* The pure models are those of the specifications of Section 4 (strings are lists of digits, level 1
  first: P_ij is 3(i - 1) + (j - 1), P₀ is 9, the star is 10).
* Time functions are definitions. The time function of a caller is written in terms of the time
  functions of its callees. Their constants are upper bounds, some with room to spare; only the
  shape matters. The lemmas `within8_tAllTiles` and `exists_tQueryCore_le` compare `tAllTiles` and
  `tQueryCore` with the expressions (8) and L ∑ α_d of the paper.
* Tries use addresses relative to the base tr of the trie area: the cell tr + a of the memory is the
  cell a of the trie array T. The area has cap cells, of which the first T.length are in use;
  nothing is assumed about the others (a new vertex clears its eleven cells); the number T.length
  is kept in the cell fp outside the area.

The routines, the pure functions that model them, and the lemmas that say what the models compute:

| number | routine | model | what is proved about the model |
|---|---|---|---|
| 40 | `nineFirst` | `nineFirst` | `head?_nineStrs`: it is the first string of `nineStrs` |
| 41 | `nineNext` | `nineNext` | `nineNext_getElem`: from string i of `nineStrs` to string i + 1 |
| 42 | `scatter` | `scatter`, `starRunIf` | `lowList` and `boxesOf` are built from them |
| 43 | `starFirst` | `starFirst`, `lastStar` | `starBoxes` is `nineStrs` mapped by `starFirst` |
| 44 | `horner` | `ofDigitList 10` | `ofDigitList_digitsT`: the code of a leaf |
| 45 | `lookup` | `trieLookup` | `TrieRep.lookup`, `TrieRep.walkOK` |
| 46 | `insert` | `trieInsert` | `TrieRep.insert`, `TrieRep.insertOK` |
| 47 | `newRoot` | `trieNew` | `TrieRep.new` |
| 48 | `sumTen` | sum of `tenValues` | `exists_lastStar_of_mem_starBoxes`, `abs_dp_partial_sum_le` |
| 49 | `fillList` | `fillTrie` | `fillTrie_rep`, `length_fillTrie_le` |
| 50 | `tile` | `tileTrie` | `fillUpTo_rep`, `length_tileTrie_le` |
| 51 | `allTiles` | `allTries` | `allTries_rep`, `length_allTries_le`, `lookup_allTries` |
| 52 | `outDigits` | `OutDigitsArgs.digits` | `digitsO_outStrOfPos`: the string of a position |
| 53 | `queryCore` | `trieQuery`, `queryTerms` | `trieQuery_allTries`, `abs_query_partial_sum_le` |

The last line of the table continues with `Theorem30.correct`. The model `boxValue` is computed by a
part of `fillList`, which calls `sumTen` for a box with stars.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## Vocabulary -/

/-! ## Procedure numbers

The numbers 0 to 39 belong to Section 2, the numbers from 40 on to Section 4. This file fixes 40 to
53; the files of the other routines of Section 4 fix theirs. -/

namespace Proc
/-- The numbers of the fourteen routines, in the order in which they call each other. -/
slots 40 nineFirst nineNext scatter starFirst horner lookup insert newRoot sumTen fillList tile
  allTiles outDigits queryCore
end Proc

/-! ## Time functions -/

/-- The routines with one loop over a string of n or L digits: a constant number of steps for each
digit. -/
def tNineFirst (n : ℕ) : ℕ := 30 * n + 30
@[inherit_doc tNineFirst] def tNineNext (n : ℕ) : ℕ := 90 * n + 60
@[inherit_doc tNineFirst] def tScatter (L : ℕ) : ℕ := 60 * L + 30
@[inherit_doc tNineFirst] def tStarFirst (L : ℕ) : ℕ := 50 * L + 30
@[inherit_doc tNineFirst] def tHorner (L : ℕ) : ℕ := 20 * L + 10
@[inherit_doc tNineFirst] def tLookup (L : ℕ) : ℕ := 20 * L + 12
@[inherit_doc tNineFirst] def tInsert (L : ℕ) : ℕ := 220 * L + 20
/-- Eleven cells are cleared. -/
def tNewRoot : ℕ := 160
/-- Ten times: write a digit, look up, add. -/
def tSumTen (L : ℕ) : ℕ := 10 * (tLookup L + 40) + 30
/-- A round for one box: stars, value (both branches are paid for), insertion, next leaf. -/
def tFillRound (L : ℕ) : ℕ :=
  tStarFirst L + tHorner L + tSumTen L + tInsert L + tNineNext L + 116
/-- One box: the test of the loop and a round. -/
def tFillStep (L : ℕ) : ℕ := tFillRound L + 4
/-- The boxes with a given number of stars, cnt of them. -/
def tFillList (L cnt : ℕ) : ℕ := tNineFirst L + cnt * tFillStep L + 60
/-- The trie of a tile: its root, then the boxes with 0, …, m - t stars. -/
def tTile (L m t : ℕ) : ℕ :=
  tNewRoot + ((List.range (m - t + 1)).map fun e => tFillList L (starBoxes L m t e).length + 60).sum
    + 60
/-- All tiles. -/
def tAllTiles (L m t nB : ℕ) : ℕ := nB * (nB * (tTile L m t + 80) + 40) + 30
@[inherit_doc tNineFirst] def tOutDigits (L : ℕ) : ℕ := 70 * L + 40
/-- A query, once the digits of its output string are known. -/
def tQueryCore (L m t : ℕ) : ℕ :=
  2 * tNineFirst m + (lowList m t []).length * (tScatter L + tHorner L + tNineNext m + 90)
    + (boxesOf m t []).length * (tScatter L + tLookup L + tNineNext m + 90) + 120

/-! ## The enumeration of the strings with a bounded number of nines -/

/-- nineFirst(a, n, lo) writes the least string of n digits with lo nines. -/
def NineFirstSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a n lo : ℕ) (μ : ℕ → ℤ), lo ≤ n → a + n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.nineFirst d [a, n, lo] μ (tNineFirst n) fun _ μ' =>
      SegN μ' a (nineFirst n lo) ∧ SameOutside μ μ' a n

/-- nineNext(a, n, lo, hi) replaces the string at a by the next one and returns 1, or leaves it and
returns 0 if it is the last one. -/
def NineNextSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a n lo hi : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ a l → l ∈ nineStrs n lo hi →
    a + n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.nineNext d [a, n, lo, hi] μ (tNineNext n) fun r μ' =>
      SegN μ' a ((nineNext lo hi l).getD l) ∧ r = (if (nineNext lo hi l).isSome then 1 else 0) ∧
        SameOutside μ μ' a n

/-! ## Strings -/

/-- scatter(w, s, out, L, star) writes at out the string at w with its nines replaced by the digits
of the string at s, whose leading nines are first turned into stars if star = 1. -/
def ScatterSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (w s out L : ℕ) (star : Bool) (wl sl : List ℕ) (μ : ℕ → ℤ), SegN μ w wl → SegN μ s sl →
    wl.length = L → sl.length = wl.count 9 → Apart out L w L → Apart out L s sl.length →
    w + L < lim.space → s + sl.length < lim.space → out + L < lim.space →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.scatter d [w, s, out, L, if star then 1 else 0] μ (tScatter L) fun _ μ' =>
      SegN μ' out (scatter wl (starRunIf star sl)) ∧ SameOutside μ μ' out L

/-- starFirst(cur, box, L, e) writes at box the string at cur with its first e nines turned into
stars; it returns the position of the last star (0 if e = 0). -/
def StarFirstSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (cur box L e : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ cur l → l.length = L → Apart box L cur L →
    cur + L < lim.space → box + L < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.starFirst d [cur, box, L, e] μ (tStarFirst L) fun r μ' =>
      SegN μ' box (starFirst e l) ∧ r = ((lastStar (starFirst e l)).getD 0 : ℕ) ∧
        SameOutside μ μ' box L

/-- horner(a, L) returns the number with the L decimal digits at a, most significant first. -/
def HornerSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (a L : ℕ) (l : List ℕ) (μ : ℕ → ℤ), SegN μ a l → l.length = L → (∀ d ∈ l, d < 10) →
    a + L < lim.space →
    (10 : ℤ) ^ L ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.horner d [a, L] μ (tHorner L) fun r μ' => r = (ofDigitList 10 l : ℕ) ∧
      μ' = μ

/-! ## Tries -/

/-! ## The dynamic program of Lemma 29 -/

/-- The arguments of fillList(e, root, aA, aB, tr, fp, cur, box, L, mt), with mt = m - t, and the
data behind them: the encodings encA and encB of the tile are at aA and aB; the trie area of cap
cells at tr holds the array T, and fp holds its length; cur and box (L cells each) are scratch. The
array is described as in `fillTrie_rep`: tile is the number of the trie (the number of the tile),
roots tile its root, old what the other tries hold, and lo the address from which the tries stand
in the array. -/
structure FillListArgs where
  (L m t : ℕ)
  (encA encB : Leaf L → ℤ)
  (aA aB tr cap fp cur box e tile lo : ℕ)
  roots : ℕ → ℕ
  old : ℕ × List ℕ → Option ℤ
  T : List ℤ

namespace FillListArgs

variable (x : FillListArgs)

end FillListArgs

/-! ## A query -/

/-- The arguments of outDigits(gI, gJ, dI, dJ, aMASK, K0, L, wd) and the data behind them: gI and gJ
are the numbers of the blocks of I and J within their bands, dI and dJ the addresses of the base-3
digits rI and rJ of their offsets, aMASK the address of the list of the subsets (a mask of L cells
for each), k0 the number of blocks of a band, L the number of levels, m of which belong to a subset,
and wd the address of the result. -/
structure OutDigitsArgs where
  (gI gJ dI dJ aMASK k0 L wd m : ℕ)
  (rI rJ : List ℕ)

namespace OutDigitsArgs

variable (x : OutDigitsArgs)

/-- The mask of the subset of the block product (gI, gJ). -/
def mask : List Bool := unrank x.L x.m (x.gI * x.k0 + x.gJ)

/-- The address of that mask in the list of the subsets. -/
def base : ℕ := x.aMASK + (x.gI * x.k0 + x.gJ) * x.L

/-- The digits of the output string: 9 at the levels of the subset, and elsewhere 3 a + b for the
next digits a of rI and b of rJ. -/
def digits : List ℕ := outDigits x.m x.mask x.rI x.rJ

end OutDigitsArgs

/-- What `outDigits` assumes: the mask of the subset and the digits of the two offsets stand in the
memory, and the L cells from wd are apart from all three. -/
structure OutDigitsPre (lim : Limits) (μ : ℕ → ℤ) (x : OutDigitsArgs) : Prop where
  std : Std lim
  m_le : x.m ≤ x.L
  gI_lt : x.gI < x.k0
  gJ_lt : x.gJ < x.k0
  index_lt : x.gI * x.k0 + x.gJ < x.L.choose x.m
  segMask : SegN μ x.base (x.mask.map fun b => if b then 1 else 0)
  segI : SegN μ x.dI x.rI
  segJ : SegN μ x.dJ x.rJ
  lenI : x.rI.length = x.L - x.m
  lenJ : x.rJ.length = x.L - x.m
  ltI : ∀ a ∈ x.rI, a < 3
  ltJ : ∀ a ∈ x.rJ, a < 3
  apartMask : Apart x.wd x.L x.base x.L
  apartI : Apart x.wd x.L x.dI (x.L - x.m)
  apartJ : Apart x.wd x.L x.dJ (x.L - x.m)
  spaceMasks : x.aMASK + x.k0 * x.k0 * x.L < lim.space
  spaceI : x.dI + x.L < lim.space
  spaceJ : x.dJ + x.L < lim.space
  spaceDest : x.wd + x.L < lim.space

/-- `outDigits` writes the digits of the output string at wd and changes nothing else. -/
def OutDigitsSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : OutDigitsArgs) (μ : ℕ → ℤ), OutDigitsPre lim μ x →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.outDigits d [x.gI, x.gJ, x.dI, x.dJ, x.aMASK, x.k0, x.L, x.wd] μ
      (tOutDigits x.L) fun _ μ' => SegN μ' x.wd x.digits ∧ SameOutside μ μ' x.wd x.L

end Light.Sec4
