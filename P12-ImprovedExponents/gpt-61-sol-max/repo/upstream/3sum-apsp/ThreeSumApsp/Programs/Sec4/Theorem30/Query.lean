/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Lang.Auto
public import ThreeSumApsp.Programs.Sec4.Theorem30.Directory
public import ThreeSumApsp.Programs.Sec4.Theorem30.RoutineFacts
public import ThreeSumApsp.Spec.Sec4.Theorem30.PartialSums

/-!
# A query, from the block that holds the data structure (proof of Theorem 30, "Query")

"Given (I, J), we find its tile from the bands of row I and column J, the subset Q of its block
product, and its output string w […], all in O(L) operations". Below, the output string is called η.
queryAt(I, J, b0) has four parts. It reads the sizes, the addresses of the tables and the bands of I
and J from the block at b0 (queryAtReads), computes the addresses of the areas of Section 4
(queryAtAreas), lets outDigits write the digits of η (queryAtOut), reads the root of the trie of the
tile from the table of roots, and lets queryCore compute the sum of Lemma 28 from the two encodings
and this trie (queryAtCore). There is one lemma for each part; for each of the two calls a record
holds the arguments (outArgs, coreArgs) and a lemma says that the block holds what the routine
assumes (outArgs_pre, coreArgs_pre). queryAt_spec puts the four parts together.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/


/-- The first part of queryAt(I, J, b0): what is read from the directory and from the table BAND. -/
def queryAtReads  :=
  .set 3 (M (v 2 +' k 0)) ;;
  .set 4 (M (v 2 +' k 1)) ;;
  .set 5 (M (v 2 +' k 31)) ;;
  .set 6 (M (v 2 +' k 4)) ;;
  .set 7 (M (v 2 +' k 7)) ;;
  .set 8 (M (v 2 +' k 9)) ;;
  .set 9 (M (v 2 +' k 10)) ;;
  .set 10 (M (v 2 +' k 22)) ;;
  .set 11 (M (v 2 +' k 23)) ;;
  .set 12 (M (v 2 +' k 24)) ;;
  .set 13 (M (v 2 +' k 30)) ;;
  .set 14 (M (v 10 +' v 0)) ;;
  .set 15 (M (v 10 +' v 1))

/-- The second part: the areas of Section 4 lie one behind the other from WD on. -/
def queryAtAreas  :=
  .set 16 (v 13 +' v 3 +' v 3) ;;
  .set 17 (v 16 +' v 3) ;;
  .set 18 (v 17 +' v 4 +' k 1) ;;
  .set 19 (v 18 +' v 8 *' v 8)

/-- The call of outDigits: the digits of the output string. -/
def queryAtOut : Stmt :=
  .call 52 [M (v 11 +' v 0), M (v 11 +' v 1),
    v 12 +' v 0 *' v 6, v 12 +' v 1 *' v 6, M (v 2 +' k 21),
    v 7, v 3, v 13] 20

/-- The call of queryCore: the sum of Lemma 28. The tile of (I, J) has the number bandI nB + bandJ,
and the root of its trie is read from the table of roots. -/
def queryAtCore : Stmt :=
  .call 53 [M (v 2 +' k 26) +' v 14 *' v 9,
    M (v 2 +' k 27) +' v 15 *' v 9, v 19,
    M (v 18 +' (v 14 *' v 8 +' v 15)), v 13, v 17, v 16, v 3, v 4,
    v 5] 0

/-- queryAt(I, J, b0) returns (XY)[I, J]: the result of a procedure is its local 0, into which the
last call stores. -/
def queryAtBody := queryAtReads ;; queryAtAreas ;; queryAtOut ;; queryAtCore

/-- What the locals hold after the first part. -/
def queryAtRead (p : Sec2.Par) (t b0 I J : ℕ) : List ℤ :=
  [I, J, b0, p.L, p.m, t, p.Lo, p.K0, p.nB, p.T, p.aBAND b0, p.aBLOCK b0, p.aDIG3 b0, aWD p b0,
    (I / (p.K0 * p.N0) : ℕ), (J / (p.K0 * p.N0) : ℕ)]

/-- What the locals hold after the second part. -/
def queryAtLocals p t b0 I J :=
  queryAtRead p t b0 I J ++ [(aBOX p b0 : ℤ), aSS p b0, aROOTS p b0, aTR p b0]

section

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : ThreeSumApsp.IntMatrix p.N (D p.m)} {Y : ThreeSumApsp.IntMatrix (D p.m) p.N}
  {U : ℤ} {μ : Light.Memory}

/-! ## The first two parts -/

variable (hlim : Lim30 lim p t b0 U)

include hlim in
/-- The second part computes the addresses of the areas of Section 4. -/
theorem queryAtAreas_spec  I J :
    Ends lim P d queryAtAreas ⟨frame (queryAtRead p t b0 I J), μ⟩ 50
      (· = ⟨frame (queryAtLocals p t b0 I J), μ⟩) := by
  light_facts hlim hlim.std
  obtain ⟨⟩ := areas p t b0
  unfold queryAtLocals queryAtRead
  -- the product nB², in the integers

  -- box := digits + L + L; str := box + L; roots := str + m + 1
  light_set (aBOX p b0 : ℕ)
  light_block []

/-! ## The call of outDigits -/

/-- Bits as natural numbers. -/
theorem segN_of_segB {μ} {a} {l} (h : Sec2.SegB μ a l) :
    SegN μ a (l.map fun b => if b then 1 else 0) := by
  unfold Sec2.SegB at h
  unfold SegN
  rw [List.map_map]
  convert h using 2
  funext b
  cases b <;> simp

/-- The arguments of the call of outDigits, and the data behind them. -/
def outArgs (p : Sec2.Par) (b0 I J : ℕ) : OutDigitsArgs :=
  ⟨I / p.N0 % p.K0, J / p.N0 % p.K0, p.aDIG3 b0 + I * p.Lo, p.aDIG3 b0 + J * p.Lo, p.aMASK b0, p.K0,
    p.L, aWD p b0, p.m, digitList 3 p.Lo (I % p.N0), digitList 3 p.Lo (J % p.N0)⟩

/-! ## The call of queryCore -/

/-- The number of the tile of the position (I, J). -/
def tileOf (p : Sec2.Par) I J := I / (p.K0 * p.N0) * p.nB + J / (p.K0 * p.N0)

/-- The arguments of the call of queryCore, and the data behind them. -/
def coreArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : ThreeSumApsp.IntMatrix p.N (D p.m)) (Y : ThreeSumApsp.IntMatrix (D p.m) p.N) (I J : ℕ) :
    QueryCoreArgs where
  L := p.L
  m := p.m
  t := t
  encA := encRow p hmL X (I / (p.K0 * p.N0))
  encB := encCol p hmL Y (J / (p.K0 * p.N0))
  η := outStrOfPos (stdLayout hmL) I J
  aA := p.aENCA b0 + I / (p.K0 * p.N0) * p.T
  aB := p.aENCB b0 + J / (p.K0 * p.N0) * p.T
  tr := aTR p b0
  root := (dsTries p t hmL X Y).root (tileOf p I J)
  wd := aWD p b0
  ss := aSS p b0
  box := aBOX p b0
  T := (dsTries p t hmL X Y).cells

include hlim in
/-- Every product of two encoded numbers fits in a word. -/
theorem abs_enc_mul_le  (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) β β' τ :
    |encRow p hmL X β τ * encCol p hmL Y β' τ| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY β β'
  rw [abs_mul]
  calc |encRow p hmL X β τ| * |encCol p hmL Y β' τ| ≤ 7 ^ p.L * U * (7 ^ p.L * U) :=
        mul_le_mul (hrow τ) (hcol τ) (abs_nonneg _) ((abs_nonneg _).trans (hrow τ))
    _ ≤ 10 ^ p.m * (7 ^ p.L * U * (7 ^ p.L * U)) :=
        le_mul_of_one_le_left (mul_self_nonneg _) (one_le_pow₀ (by norm_num))
    _ ≤ lim.word := hlim.value

section

variable (I J : Fin p.N)

/-- The tile of the position (I, J) is one of the nB² tiles. -/
theorem tileOf_lt (hmL : p.m ≤ p.L) : tileOf p I J < p.nB * p.nB :=
  Nat.mul_add_lt_mul (bandOf_lt_numBands hmL p.N I I.isLt) (bandOf_lt_numBands hmL p.N J J.isLt)

/-- It is given by the encodings of the band of I and of the band of J. -/
theorem getElem?_tileOf :
    (tileList p.nB (encRow p hmL X) (encCol p hmL Y))[tileOf p I J]?
      = some ⟨arrT (coreArgs p t hmL b0 X Y I J).encA, arrT (coreArgs p t hmL b0 X Y I J).encB⟩ :=
  getElem?_tileList p.nB _ _ (bandOf_lt_numBands hmL p.N I I.isLt)
    (bandOf_lt_numBands hmL p.N J J.isLt)

variable (ht : t ≤ p.m)

include ht

/-- Every box of the query is found in the trie of the tile. -/
theorem coreArgs_walk l
    (hl : l ∈ boxesOf p.m t (digitsO (coreArgs p t hmL b0 X Y I J).η)) :
    WalkOK (coreArgs p t hmL b0 X Y I J).T (coreArgs p t hmL b0 X Y I J).root l :=
  walkOK_allTries ht (getElem?_tileOf (t := t) (b0 := b0) I J)
    (card_innerSetO_outStrOfPos (stdLayout hmL) I J) hl

/-- Every partial sum of the query fits in a word. -/
theorem coreArgs_sums (hlim : Lim30 lim p t b0 U) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) j :
    |((coreArgs p t hmL b0 X Y I J).terms.take j).sum| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY (I / (p.K0 * p.N0))
    (J / (p.K0 * p.N0))
  have hcard := card_innerSetO_outStrOfPos (stdLayout hmL) I J
  have hterms := queryTerms_allTries ht
    (getElem?_tileOf (t := t) (hmL := hmL) (b0 := b0) (X := X) (Y := Y) I J) hcard
  rw [QueryCoreArgs.terms]
  exact (congrArg (fun l => |(l.take j).sum|) hterms).trans_le
    ((abs_query_partial_sum_le hrow hcol ht hcard j).trans hlim.value)

/-- What queryCore returns for the tile of (I, J) is (XY)[I, J], by Theorem 30. -/
theorem coreArgs_value :
    trieQuery p.m t (arrT (coreArgs p t hmL b0 X Y I J).encA)
      (arrT (coreArgs p t hmL b0 X Y I J).encB) (coreArgs p t hmL b0 X Y I J).T
      (coreArgs p t hmL b0 X Y I J).root (digitsO (coreArgs p t hmL b0 X Y I J).η) = (X * Y) I J :=
  (trieQuery_allTries ht _ _ (getElem?_tileOf I J)
    (card_innerSetO_outStrOfPos (stdLayout hmL) I J)).trans
    (Theorem30.correct t ht (stdLayout hmL) X Y I J)

end

/-! ## The routine -/

end

end Light.Sec4
