/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# Theorem 30 in the light language: the memory map and the invariant of the data structure

The data structure occupies one block of the memory, from a base address b0 on. First comes the
shared block of Section 2 (directory, tables, the encodings of all bands), and behind it the areas
of Section 4:

    WD (L) | CUR (L) | BOX (L) | SS (m) | FP (1) | ROOTS (nB²) | TR (cap)

WD holds the digits of the output string of a query; CUR, BOX and SS are scratch strings; FP holds
the length of the trie array; ROOTS holds the roots of the tries, that of tile (β, β') in the cell
β nB + β'; TR is the trie area. Cell 31 of the directory holds t. `Areas` says where the tables that
the routines of Section 4 read and the areas of Section 4 lie, and `areas` proves it.

Two routines know this map: preCore(L, m, t, N, D, aX, aY, b0) builds the block from the matrices at
aX and aY, which lie below b0, and queryAt(I, J, b0) answers a query from it. They are relocatable,
so that Theorem 30, its offline form and Corollary 26 use the same two routines. The main procedures
of Theorem 30's programs only read the sizes from the input and compute the addresses. For Corollary
26 a routine of its own stands in between: it finds m and, from the threshold of the proof on, L and
t, writes padded copies of the matrices, and runs `preCore` on them.

Section 4.3: "Our data structure consists of three components: the list of the K₀² subsets Q
assigned to the block products of a tile […], the encodings of all row bands and all column bands,
and for every tile, the values of all its boxes". In the invariant DSReady the field shared holds
the first two, and the fields roots and trie hold the third: "for each tile we store its boxes, with
their values, in a standard trie on their strings of L symbols". The tries of all tiles lie in one
array (trie), and the table roots has the root of the trie of each tile. The invariant depends only
on the cells from b0 on, without the scratch strings (`DSReady.congr`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The map -/

/-- The digits of the output string of a query: L cells. -/
def aWD (p : Sec2.Par) (b0 : ℕ) : ℕ := p.sharedEnd b0
/-- Scratch of the preprocessing, the current leaf: L cells. -/
def aCUR (p : Sec2.Par) (b0 : ℕ) : ℕ := aWD p b0 + p.L
/-- Scratch, the current box: L cells. -/
def aBOX (p : Sec2.Par) (b0 : ℕ) : ℕ := aCUR p b0 + p.L
/-- Scratch of a query, the current string on the levels of Q: m cells. -/
def aSS (p : Sec2.Par) (b0 : ℕ) : ℕ := aBOX p b0 + p.L
/-- The first base-11 page, immediately after the scratch strings. -/
def aPage (p : Sec2.Par) (b0 : ℕ) := aSS p b0 + p.m

def pageCells (p : Sec2.Par) := p.nB * p.nB * (p.T * p.T)

/-- Keep one guard cell so even the end pointers fit. -/
def top (p : Sec2.Par) (_t b0 : ℕ) := aPage p b0 + pageCells p + 1

/-! ## Where the areas lie -/

/-- What the routines of Section 4 need of the map: the tables that they read lie one behind the
other between the directory and WD, and the areas of Section 4 behind WD. -/
structure Areas (p : Sec2.Par) (t b0 : ℕ) : Prop where
  dir : b0 + 32 ≤ p.aMASK b0
  mask : p.aMASK b0 + p.KK * p.L = p.aBAND b0
  band : p.aBAND b0 + p.N = p.aBLOCK b0
  block : p.aBLOCK b0 + p.N = p.aDIG3 b0
  dig3 : p.aDIG3 b0 + p.N * p.Lo ≤ p.aENCA b0
  enca : p.aENCA b0 + p.nB * p.T = p.aENCB b0
  encb : p.aENCB b0 + p.nB * p.T ≤ aWD p b0
  cur : aCUR p b0 = aWD p b0 + p.L
  box : aBOX p b0 = aWD p b0 + 2 * p.L
  ss : aSS p b0 = aWD p b0 + 3 * p.L
  page : aPage p b0 = aWD p b0 + 3 * p.L + p.m
  top : top p t b0 = aPage p b0 + pageCells p + 1

/-- The tables and the areas lie as Areas says. -/
theorem areas (p : Sec2.Par) (t b0 : ℕ) : Areas p t b0 := by
  have hplaces := p.places b0
  constructor <;> (try simp [aPage,aSS,aBOX,aCUR,aWD,top]) <;> omega

/-- The directory lies before the areas of Section 4. -/
theorem wd_ge (p : Sec2.Par) (b0 : ℕ) : b0 + 32 ≤ aWD p b0 := by
  obtain ⟨⟩ := areas p 0 b0
  omega

/-- The shared block ends behind its base address. -/
theorem base_le_sharedEnd (p : Sec2.Par) (b0 : ℕ) : b0 ≤ p.sharedEnd b0 :=
  (Nat.le_add_right b0 32).trans (wd_ge p b0)

/-- The block holds more than its directory. -/
theorem base_add_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 + 32 < top p t b0 := by
  obtain ⟨⟩ := areas p t b0
  omega

/-- The block is not empty. -/
theorem base_lt_top (p : Sec2.Par) (t b0 : ℕ) : b0 < top p t b0 :=
  (Nat.le_add_right b0 32).trans_lt (base_add_lt_top p t b0)

/-- The scratch strings of a query lie in the block. -/
theorem scratch_in_block (p : Sec2.Par) (t b0 : ℕ) :
    b0 ≤ aWD p b0 ∧ aWD p b0 + (3 * p.L + p.m) ≤ top p t b0 := by
  obtain ⟨⟩ := areas p t b0
  omega

/-! ## The directory -/

namespace Dir

/-- The cells of the directory, the first 32 cells of the block, that the routines of Section 4 use.
They hold L, m, L - m, K₀, nB, 10^L, the addresses of the tables MASK, BAND, BLOCK, DIG3 and of the
encodings ENCA, ENCB, the end of the shared block (which is the address of WD), and t. All but the
last are written by the shared stage. -/
slots 0 levels inner
@[inherit_doc levels] abbrev outer : ℕ := 4
@[inherit_doc levels] abbrev blocks : ℕ := 7
slots 9 bands leaves
slots 21 mask band block digits
slots 26 encA encB
slots 30 sharedEnd switch

end Dir

/-! ## The invariant -/

/-- The encoding of the row band β. -/
def encRow (p : Sec2.Par) (hmL : p.m ≤ p.L) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (β : ℕ) : Leaf p.L → ℤ :=
  encodingL (bandArrayL (stdLayout hmL) X β)

/-- The encoding of the column band β. -/
def encCol (p : Sec2.Par) (hmL : p.m ≤ p.L) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ)
    (β : ℕ) : Leaf p.L → ℤ :=
  encodingR (bandArrayR (stdLayout hmL) Y β)

/-- The limits that the two routines need: U bounds the entries of X and Y. -/
structure Lim30 (lim : Limits) (p : Sec2.Par) (t b0 : ℕ) (U : ℤ) : Prop where
  std : Std lim
  space : top p t b0 ≤ lim.space
  /-- Every value and every partial sum fits in a word. -/
  value : 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ lim.word
  /-- The shared stage can compute the encodings. -/
  enc : 7 ^ (p.L + 1) * U ≤ lim.word
  /-- The shared stage can compute the table of the powers of 10. -/
  pow : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word

/-! ## The two routines that know the map -/

/-- The numbers of the two routines. -/
slots 54 Proc.preCore Proc.queryAt

/-- The time of `queryAt`. -/
def tQueryAt (L m t : ℕ) : ℕ := tOutDigits L + tQueryCore L m t + 400

end Light.Sec4
