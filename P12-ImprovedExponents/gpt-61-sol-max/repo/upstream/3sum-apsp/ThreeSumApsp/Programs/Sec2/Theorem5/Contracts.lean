/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Lang.Lib.PowTable
public import ThreeSumApsp.Programs.Sec2.Theorem5.Places
public import ThreeSumApsp.Spec.Sec2.Theorem5.Layout
public import ThreeSumApsp.Spec.Sec2.Theorem5.Arrays
public import ThreeSumApsp.Sec2.Lemma10
public import ThreeSumApsp.Spec.Sec2.Theorem5.Alphabets
public import Mathlib.Data.List.TakeWhile

/-!
# Theorem 5 in the light language: the map

One file that fixes everything on which two routines have to agree, besides the sizes and the places
of the arrays: the numbers of the procedures, and for every procedure its arguments, what it needs,
what it leaves behind, which cells it may change, and the shape of its running time. A routine is
proved against its own entry; a caller assumes the entries of the routines it calls. So the proof of
a routine does not depend on the proofs of the routines that it calls.

* Routines never contain an address.  They receive scalars and base addresses as arguments.  Only
  the two main routines (Theorem 5 here, the data structure of Section 4) know the places.
* The stages up to the encodings of all bands are shared with Section 4: procedure pShared fills the
  shared block, which starts at an address b0 above the input and the output of the program that
  calls it (the free pointer).
* An entry XSpec lim P c says: in the program P, within the limits lim, procedure number pX does its
  job within c times the shape of its running time (Meets).  The theorem on a routine proves its
  entry for every c from the constant of the routine on, so a caller can assume several entries at
  one constant.
* The entries of encStep, encodeBands, countSort, copy, runTiles and report stand with these
  routines.
* Strings are numbers: a string over an alphabet of b symbols is its code in base b, level 1 most
  significant (namespace Spec).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## Vocabulary -/

/-- The cells from a on hold a list of bits, as 1 and 0. -/
def SegB (μ : Light.Memory) (a : ℕ) (l : List Bool) : Prop :=
  Seg μ a (l.map fun b => if b then 1 else 0)

/-- A cell of a segment of bits. -/
def SegB.get {μ} {a} {l} (h : SegB μ a l) {q} (hq : q < l.length) :=
  (Seg.getD h (by rwa [List.length_map]) 0).trans (List.getD_map_of_lt _ hq false 0)

/-! ## The numbers of the procedures

Number 0 is empty.  1 to 25: the shared routines and those of Theorem 5.  26 to 28: the test of the
regime, the brute force, and the solver for all instances.  29 to 39 are not used.  From 40 on:
Section 4. -/

/-- The number of pow. -/
def pPow := 2
/-- The number of binom. -/
def pBinom := 3
/-- The number of sqrt. -/
def pSqrt := 4
/-- The number of subsets. -/
def pSubsets := 5
/-- The number of counters. -/
def pCounters := 6
/-- The number of digits. -/
def pDigits := 7
/-- The number of coef. -/
def pCoef := 8
/-- The number of bandArray. -/
def pBandArray := 9
/-- The number of encStep. -/
def pEncStep := 10
/-- The number of the brute force. -/
def pThinBrute := 27

/-! ## The entries of the shared routines -/

section

variable (lim : Limits) (P : Program) (c : ℕ)

/-- pow(b, n, dst): writes b^0, …, b^n to dst. -/
def PowSpec :=
  ∀ (b n dst : ℕ) (μ : Light.Memory),
    1 ≤ dst → dst + n + 1 ≤ lim.space → 1 ≤ b →
    ((b ^ (n + 1) : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pPow d [b, n, dst] μ (c * (n + 1)) fun _ μ' =>
      Seg μ' dst (powList b (n + 1)) ∧ SameOutside μ μ' dst (n + 1)

/-- binom(L, m, pas): returns binom(L, m), by Pascal's triangle in the L + 2 cells from pas. -/
def BinomSpec : Prop :=
  ∀ (L m pas : ℕ) (μ : Light.Memory),
    pas + L + 2 ≤ lim.space → m ≤ L → ((2 ^ L : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pBinom d [L, m, pas] μ (c * (L + 1) ^ 2) fun r μ' =>
      r = L.choose m ∧ SameOutside μ μ' pas (L + 2)

/-- sqrt(K): returns ⌊√K⌋, by counting up.  Changes no cell. -/
def SqrtSpec : Prop :=
  ∀ (K : ℕ) (μ : Light.Memory),
    ((4 * K + 4 : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pSqrt d [K] μ (c * (Nat.sqrt K + 1)) fun r μ' =>
      r = Nat.sqrt K ∧ μ' = μ

/-- subsets(L, m, KK, mask): writes the first KK subsets of size m of the L levels, as rows of L
bits, in the order of Spec.unrank. -/
def SubsetsSpec :=
  ∀ (L m KK mask : ℕ) (μ : Light.Memory),
    mask + KK * L ≤ lim.space → m ≤ L → KK ≤ L.choose m →
    ((KK + L : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P pSubsets d [L, m, KK, mask] μ (c * ((KK + 1) * (L + 1))) fun _ μ' =>
      (∀ s < KK, SegB μ' (mask + s * L) (Spec.unrank L m s)) ∧ SameOutside μ μ' mask (KK * L)

/-- counters(N, K0, N0, band): for every row I < N writes its band I / (K0 N0) to band + I and its
block I / N0 % K0 to band + N + I, by counting. -/
def CountersSpec : Prop :=
  ∀ (N K0 N0 band : ℕ) (μ : Light.Memory),
    band + 2 * N ≤ lim.space → 0 < K0 → 0 < N0 →
    ((K0 + N0 : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pCounters d [N, K0, N0, band] μ (c * (N + 1)) fun _ μ' =>
      (∀ I < N, μ' (band + I) = (I / (K0 * N0) : ℕ) ∧ μ' (band + N + I) = (I / N0 % K0 : ℕ))
      ∧ SameOutside μ μ' band (2 * N)

/-- digits(n, b, len, dst): for every x < n writes the len digits of x % b^len in base b, most
significant first, to dst + x len, by an odometer. -/
def DigitsSpec :=
  ∀ (n b len dst : ℕ) (μ : Light.Memory),
    dst + n * len ≤ lim.space → 2 ≤ b → (b : ℤ) ≤ lim.word →
    (n : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P pDigits d [n, b, len, dst] μ (c * ((n + 1) * (len + 1))) fun _ μ' =>
      (∀ x < n, SegN μ' (dst + x * len) (ThreeSumApsp.digitList b len (x % b ^ len)))
      ∧ SameOutside μ μ' dst (n * len)

/-- coef(phi): writes the 70 coefficients φ_λ(s) to phi and the 70 coefficients ψ_λ(t) to phi + 70.
-/
def CoefSpec :=
  ∀ (phi : ℕ) (μ : Light.Memory),
    phi + 140 ≤ lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P pCoef d [phi] μ c fun _ μ' =>
      Seg μ' phi Spec.phiFlat ∧ Seg μ' (phi + 70) Spec.psiFlat
      ∧ SameOutside μ μ' phi 140

/-- What bandArray reads, apart from the matrix: the table of subsets and the two tables of digits,
all below the array it writes. -/
structure BandTables (p : Par) (μ : Light.Memory) (mask dig3 dig4 arr : ℕ) : Prop where
  hmask : ∀ s < p.KK, SegB μ (mask + s * p.L) (Spec.unrank p.L p.m s)
  hdig3 : ∀ I < p.N, SegN μ (dig3 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % p.N0))
  hdig4 : ∀ x < p.D, SegN μ (dig4 + x * p.m) (ThreeSumApsp.digitList 4 p.m x)
  mask_le : mask + p.KK * p.L ≤ arr
  dig3_le : dig3 + p.N * p.Lo ≤ arr
  dig4_le : dig4 + p.D * p.m ≤ arr

/-- The shape of the running time of bandArray: clear 7^L cells, then one entry in O(L) steps for
each subset of the table, each row of a block and each column. -/
def bandArrayShape (p : Par) := p.S7 + (p.KK * p.N0 * p.D + 1) * (p.L + 1)

/-- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr), for the left
side: side = 0, aA the address of X, sI = D, sK = 1 (sI and sK are the strides of the index I of the
band and of the inner index k: the entry is at aA + I sI + k sK).  Writes the input array of the row
band β (Section 2.3.4), in the order of the codes, to arr. -/
def BandArrayLSpec :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (β aX mask dig3 dig4 arr : ℕ) (μ : Light.Memory)
    (X : ThreeSumApsp.IntMatrix p.N (ThreeSumApsp.D p.m)),
    arr + p.S7 ≤ lim.space → MatAt μ aX X → aX + p.N * p.D ≤ arr →
    BandTables p μ mask dig3 dig4 arr → β < p.nB →
    ∀ d, d ≤ lim.depth → Meets lim P pBandArray d
      [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, 0, aX, p.D, 1, mask, dig3, dig4, arr] μ
      (c * bandArrayShape p) fun _ μ' =>
      Seg μ' arr (Spec.arrL (bandArrayL (Spec.stdLayout hmL) X β)) ∧ SameOutside μ μ' arr p.S7

/-- The same procedure for the right side: side = 1, aA the address of Y, sI = 1, sK = N. Writes the
input array of the column band β. -/
def BandArrayRSpec :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (β aY mask dig3 dig4 arr : ℕ) (μ : Light.Memory)
    (Y : ThreeSumApsp.IntMatrix (ThreeSumApsp.D p.m) p.N),
    arr + p.S7 ≤ lim.space → MatAt μ aY Y → aY + p.D * p.N ≤ arr →
    BandTables p μ mask dig3 dig4 arr → β < p.nB →
    ∀ d, d ≤ lim.depth → Meets lim P pBandArray d
      [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, 1, aY, 1, p.N, mask, dig3, dig4, arr] μ
      (c * bandArrayShape p) fun _ μ' =>
      Seg μ' arr (Spec.arrR (bandArrayR (Spec.stdLayout hmL) Y β)) ∧ SameOutside μ μ' arr p.S7

/-- Where encode finds its tables and its areas: the tables lie below dst, the 10^n cells of dst
below src, the 7^n cells of src below scr, and scr has 7^n cells. -/
structure EncodePlaces (n Lmax src dst scr tab p7 p10 : ℕ) (μ : Light.Memory) : Prop where
  n_le : n ≤ Lmax
  hp7 : Seg μ p7 (powList 7 (Lmax + 1))
  hp10 : Seg μ p10 (powList 10 (Lmax + 1))
  tab_le : tab + 70 ≤ dst
  p7_le : p7 + Lmax + 1 ≤ dst
  p10_le : p10 + Lmax + 1 ≤ dst
  dst_le : dst + 10 ^ n ≤ src
  src_le : src + 7 ^ n ≤ scr
  scr_le : scr + 7 ^ n ≤ lim.space

/-! ## The shared stage -/

/-- The tables of the powers of 3, 4, 7 and 10 in the shared block. -/
structure PowTables (p : Par) (b0 : ℕ) (μ : Light.Memory) : Prop where
  p3 : Seg μ (p.aP3 b0) (powList 3 (p.L + 1))
  p4 : Seg μ (p.aP4 b0) (powList 4 (p.L + 1))
  p7 : Seg μ (p.aP7 b0) (powList 7 (p.L + 1))
  p10 : Seg μ (p.aP10 b0) (powList 10 (p.L + 1))

/-- The other tables of the shared block: the coefficients, the subsets, the band and the block of
every row, and the digits of the offsets and of the inner indices. -/
structure RowTables (p : Par) (b0 : ℕ) (μ : Light.Memory) : Prop where
  phi : Seg μ (p.aPHI b0) Spec.phiFlat
  psi : Seg μ (p.aPSI b0) Spec.psiFlat
  mask : ∀ s < p.KK, SegB μ (p.aMASK b0 + s * p.L) (Spec.unrank p.L p.m s)
  band : ∀ I < p.N, μ (p.aBAND b0 + I) = (I / (p.K0 * p.N0) : ℕ)
  block : ∀ I < p.N, μ (p.aBLOCK b0 + I) = (I / p.N0 % p.K0 : ℕ)
  dig3 : ∀ I < p.N, SegN μ (p.aDIG3 b0 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % p.N0))
  dig4 : ∀ x < p.D, SegN μ (p.aDIG4 b0 + x * p.m) (ThreeSumApsp.digitList 4 p.m x)

/-- The tables of the shared block, all in one memory. -/
structure SharedTables (p : Par) (b0 : ℕ) (μ : Light.Memory) : Prop
  extends PowTables p b0 μ, RowTables p b0 μ

/-- The shape of the running time of the shared stage. -/
def sharedShape p :=
  (p.L + 1) ^ 2 + Nat.sqrt p.K + 1 + (p.KK + 1) * (p.L + 1) + (p.N + 1) * (p.Lo + 1)
    + (p.D + 1) * (p.m + 1)
    + p.nB * (p.T + bandArrayShape p)

/-- What the shared stage assumes: the shared block fits in the memory, X and Y stand below it, V
bounds their entries, and the encoded numbers and the powers of ten fit in a word. -/
structure SharedPre (p : Par) (aX aY b0 : ℕ) (X : ThreeSumApsp.IntMatrix p.N (ThreeSumApsp.D p.m))
    (Y : ThreeSumApsp.IntMatrix (ThreeSumApsp.D p.m) p.N) (V : ℤ) (μ : Light.Memory) : Prop where
  space : p.sharedEnd b0 ≤ lim.space
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  belowX : aX + p.N * p.D ≤ b0
  belowY : aY + p.D * p.N ≤ b0
  absX : ∀ i j, |X i j| ≤ V
  absY : ∀ i j, |Y i j| ≤ V
  seven : 7 ^ (p.L + 1) * V ≤ lim.word
  ten : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word

/-! ## Theorem 5 -/


end

end Light.Sec2
