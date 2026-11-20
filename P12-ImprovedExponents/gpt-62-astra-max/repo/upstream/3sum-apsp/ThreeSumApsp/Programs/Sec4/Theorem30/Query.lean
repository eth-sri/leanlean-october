/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

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

namespace QueryAt

/-- The local variables of queryAt: the arguments I, J, b0; the sizes L, m, t, L - m, K₀, nB, 10^L;
the addresses of the tables BAND, BLOCK, DIG3 and of the area WD; the bands of I and J; the
addresses of the areas BOX, SS, ROOTS, TR; and a local for the result of outDigits, which is not
used. -/
slots 0 Row Col Base Levels Inner Switch Outer Blocks Bands Leaves BandTab BlockTab DigitTab
  Digits BandI BandJ Box Str Pages Void

end QueryAt

open QueryAt in
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

open QueryAt in
/-- The second part: the areas of Section 4 lie one behind the other from WD on. -/
def queryAtAreas : Stmt :=
  .set Box (v Digits +' v Levels +' v Levels) ;;
  .set Str (v Box +' v Levels) ;;
  .set Pages (v Str +' v Inner)

open QueryAt in
/-- The call of outDigits: the digits of the output string. -/
def queryAtOut : Stmt :=
  .call Proc.outDigits [M (v BlockTab +' v Row), M (v BlockTab +' v Col),
    v DigitTab +' v Row *' v Outer, v DigitTab +' v Col *' v Outer, M (v Base +' k Dir.mask),
    v Blocks, v Levels, v Digits] Void

open QueryAt in
/-- The call of queryCore: the sum of Lemma 28. The tile of (I, J) has the number bandI nB + bandJ,
and the root of its trie is read from the table of roots. -/
def queryAtCore : Stmt :=
  .call Proc.queryCore [M (v Base +' k Dir.encA) +' v BandI *' v Leaves,
    M (v Base +' k Dir.encB) +' v BandJ *' v Leaves, 
    v Pages +' (v BandI *' v Bands +' v BandJ) *' (v Leaves *' v Leaves), v Digits, v Str, v Box, v Levels, v Inner,
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
  queryAtRead p t b0 I J ++ [(aBOX p b0 : ℤ), aSS p b0, aPage p b0]

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
  light_set (aBOX p b0 : ℕ)
  light_set (aSS p b0 : ℕ)
  light_set (aPage p b0)
  rfl

/-! ## The call of outDigits -/

/-- Bits as natural numbers. -/
theorem segN_of_segB {μ } {a } {l } (h : Sec2.SegB μ a l) :
    SegN μ a (l.map fun b => if b then 1 else 0) := by
  unfold Sec2.SegB at h
  unfold SegN
  rw [List.map_map]
  convert h using 2
  funext b
  simp

/-- The arguments of the call of outDigits, and the data behind them. -/
def outArgs (p : Sec2.Par) (b0 I J : ℕ) : OutDigitsArgs :=
  ⟨I / p.N0 % p.K0, J / p.N0 % p.K0, p.aDIG3 b0 + I * p.Lo, p.aDIG3 b0 + J * p.Lo, p.aMASK b0, p.K0,
    p.L, aWD p b0, p.m, digitList 3 p.Lo (I % p.N0), digitList 3 p.Lo (J % p.N0)⟩

/-- Every product of two encoded numbers fits in a word. -/
theorem abs_enc_mul_le (hlim : Lim30 lim p t b0 U) (hU : 0 ≤ U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (β β' : ℕ) (τ : Leaf p.L) :
    |encRow p hmL X β τ * encCol p hmL Y β' τ| ≤ lim.word := by
  obtain ⟨hrow, hcol⟩ := abs_enc_le hmL X Y U hU hX hY β β'
  rw [abs_mul]
  calc |encRow p hmL X β τ| * |encCol p hmL Y β' τ| ≤ (7 ^ p.L * U) * (7 ^ p.L * U) :=
        mul_le_mul (hrow τ) (hcol τ) (abs_nonneg _) ((abs_nonneg _).trans (hrow τ))
    _ ≤ 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) :=
        le_mul_of_one_le_left (mul_self_nonneg _) (one_le_pow₀ (by norm_num))
    _ ≤ lim.word := hlim.value

end Proof
end Light.Sec4
