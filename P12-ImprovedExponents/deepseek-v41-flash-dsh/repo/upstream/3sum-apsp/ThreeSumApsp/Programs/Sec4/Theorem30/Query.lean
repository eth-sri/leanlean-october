/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Directory
public import ThreeSumApsp.Programs.Sec4.Theorem30.RoutineFacts
public import ThreeSumApsp.Spec.Sec4.Theorem30.PartialSums
public import ThreeSumApsp.TacticsShort

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

namespace QueryAt

/-- The local variables of queryAt: the arguments I, J, b0; the sizes L, m, t, L - m, K₀, nB, 10^L;
the addresses of the tables BAND, BLOCK, DIG3 and of the area WD; the bands of I and J; the
addresses of the areas BOX, SS, ROOTS, TR; and a local for the result of outDigits, which is not
used. -/
abbrev Row : ℕ := 0
 abbrev Col : ℕ := 1
 abbrev Base : ℕ := 2
 abbrev Levels : ℕ := 3
 abbrev Inner : ℕ := 4
 abbrev Switch : ℕ := 5
 abbrev Outer : ℕ := 6
 abbrev Blocks : ℕ := 7
 abbrev Bands : ℕ := 8
 abbrev Leaves : ℕ := 9
 abbrev BandTab : ℕ := 10
 abbrev BlockTab : ℕ := 11
 abbrev DigitTab : ℕ := 12
 abbrev Digits : ℕ := 13
 abbrev BandI : ℕ := 14
 abbrev BandJ : ℕ := 15
 abbrev Box : ℕ := 16
 abbrev Str : ℕ := 17
 abbrev Roots : ℕ := 18
 abbrev Tries : ℕ := 19
 abbrev Void : ℕ := 20

end QueryAt

open QueryAt
/-- The first part of queryAt(I, J, b0): what is read from the directory and from the table BAND. -/
def queryAtReads : Stmt :=
  .set Levels (M (v Base +' k Dir.levels)) ;;
  .set Inner (M (v Base +' k Dir.inner)) ;;
  .set Switch (M (v Base +' k Dir.switch)) ;;
  .set Outer (M (v Base +' k Dir.outer)) ;;
  .set Blocks (M (v Base +' k Dir.blocks)) ;;
  .set Bands (M (v Base +' k Dir.bands)) ;;
  .set Leaves (M (v Base +' k Dir.leaves)) ;;
  .set BandTab (M (v Base +' k Dir.band)) ;;
  .set BlockTab (M (v Base +' k Dir.block)) ;;
  .set DigitTab (M (v Base +' k Dir.digits)) ;;
  .set Digits (M (v Base +' k Dir.sharedEnd)) ;;
  .set BandI (M (v BandTab +' v Row)) ;;
  .set BandJ (M (v BandTab +' v Col))

open QueryAt
/-- The second part: the areas of Section 4 lie one behind the other from WD on. -/
def queryAtAreas : Stmt :=
  .set Box (v Digits +' v Levels +' v Levels) ;;
  .set Str (v Box +' v Levels) ;;
  .set Roots (v Str +' v Inner +' k 1) ;;
  .set Tries (v Roots +' v Bands *' v Bands)

open QueryAt
/-- The call of outDigits: the digits of the output string. -/
def queryAtOut : Stmt :=
  .call Proc.outDigits [M (v BlockTab +' v Row), M (v BlockTab +' v Col),
    v DigitTab +' v Row *' v Outer, v DigitTab +' v Col *' v Outer, M (v Base +' k Dir.mask),
    v Blocks, v Levels, v Digits] Void

open QueryAt
/-- The call of queryCore: the sum of Lemma 28. The tile of (I, J) has the number bandI nB + bandJ,
and the root of its trie is read from the table of roots. -/
def queryAtCore : Stmt :=
  .call Proc.queryCore [M (v Base +' k Dir.encA) +' v BandI *' v Leaves,
    M (v Base +' k Dir.encB) +' v BandJ *' v Leaves, v Tries,
    M (v Roots +' (v BandI *' v Bands +' v BandJ)), v Digits, v Str, v Box, v Levels, v Inner,
    v Switch] Row

/-- queryAt(I, J, b0) returns (XY)[I, J]: the result of a procedure is its local 0, into which the
last call stores. -/
def queryAtBody : Stmt := queryAtReads ;; queryAtAreas ;; queryAtOut ;; queryAtCore

/-- What the locals hold after the first part. -/
def queryAtRead (p : Sec2.Par) (t b0 I J : ℕ) : List ℤ :=
  [I, J, b0, p.L, p.m, t, p.Lo, p.K0, p.nB, p.T, p.aBAND b0, p.aBLOCK b0, p.aDIG3 b0, aWD p b0,
    (I / (p.K0 * p.N0) : ℕ), (J / (p.K0 * p.N0) : ℕ)]

/-- What the locals hold after the second part. -/
def queryAtLocals (p : Sec2.Par) (t b0 I J : ℕ) : List ℤ :=
  queryAtRead p t b0 I J ++ [(aBOX p b0 : ℤ), aSS p b0, aROOTS p b0, aTR p b0]

section Proof

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The first two parts -/

/-- The second part computes the addresses of the areas of Section 4. -/
theorem queryAtAreas_spec (hlim : Lim30 lim p t b0 U) (I J : ℕ) :
    Ends lim P d queryAtAreas ⟨frame (queryAtRead p t b0 I J), μ⟩ 50
      (· = ⟨frame (queryAtLocals p t b0 I J), μ⟩) := by
  light_facts hlim hlim.std
  obtain ⟨⟩ := areas p t b0
  unfold queryAtLocals queryAtRead
  -- the product nB², in the integers
  have htr : ((aROOTS p b0 + p.nB * p.nB : ℕ) : ℤ) = aTR p b0 := by
    exact_mod_cast (by omega : aROOTS p b0 + p.nB * p.nB = aTR p b0)
  push_cast at htr
  -- box := digits + L + L; str := box + L; roots := str + m + 1
  light_set (aBOX p b0 : ℕ)
  light_set (aSS p b0 : ℕ)
  light_set (aROOTS p b0 : ℕ)
  -- tries := roots + nB nB
  light_set (aTR p b0 : ℕ)
  rfl

/-! ## The call of outDigits -/

/-- Bits as natural numbers. -/
theorem segN_of_segB {μ : ℕ → ℤ} {a : ℕ} {l : List Bool} (h : Sec2.SegB μ a l) :
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
def tileOf (p : Sec2.Par) (I J : ℕ) : ℕ := I / (p.K0 * p.N0) * p.nB + J / (p.K0 * p.N0)

/-- The arguments of the call of queryCore, and the data behind them. -/
def coreArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (I J : ℕ) :
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

/-- Every product of two encoded numbers fits in a word. -/
theorem abs_enc_mul_le (hlim : Lim30 lim p t b0 U) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (β β' : ℕ) (τ : Leaf p.L) :
    |encRow p hmL X β τ * encCol p hmL Y β' τ| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY β β'
  rw [abs_mul]
  calc |encRow p hmL X β τ| * |encCol p hmL Y β' τ| ≤ (7 ^ p.L * U) * (7 ^ p.L * U) :=
        mul_le_mul (hrow τ) (hcol τ) (abs_nonneg _) ((abs_nonneg _).trans (hrow τ))
    _ ≤ 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) :=
        le_mul_of_one_le_left (mul_self_nonneg _) (one_le_pow₀ tac_norm_num)
    _ ≤ lim.word := hlim.value

section Tile

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
theorem coreArgs_walk (l : List ℕ)
    (hl : l ∈ boxesOf p.m t (digitsO (coreArgs p t hmL b0 X Y I J).η)) :
    WalkOK (coreArgs p t hmL b0 X Y I J).T (coreArgs p t hmL b0 X Y I J).root l :=
  walkOK_allTries ht (getElem?_tileOf (t := t) (b0 := b0) I J)
    (card_innerSetO_outStrOfPos (stdLayout hmL) I J) hl

/-- Every partial sum of the query fits in a word. -/
theorem coreArgs_sums (hlim : Lim30 lim p t b0 U) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (j : ℕ) :
    |((coreArgs p t hmL b0 X Y I J).terms.take j).sum| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY ((I : ℕ) / (p.K0 * p.N0))
    ((J : ℕ) / (p.K0 * p.N0))
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

end Tile

/-! ## The routine -/

end Proof

end Light.Sec4