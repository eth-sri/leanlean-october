module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Tactics
public import Mathlib.Data.Int.SuccPred
public import ThreeSumApsp.Sec2.Tiling
public import Mathlib.Data.Nat.Choose.Bounds
public import ThreeSumApsp.Spec.Sec2.Theorem5.Layout
public import ThreeSumApsp.Spec.Sec2.Theorem5.Arrays
public import ThreeSumApsp.Sec2.Lemma10
public import Mathlib.Data.List.TakeWhile

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/


namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The pure model: the powers 1, b, …, b^(L-1). -/
def powList (b L : ℕ) : List ℤ := (List.range L).map fun j => ((b ^ j : ℕ) : ℤ)

@[simp] theorem length_powList (b L : ℕ) : (powList b L).length = L := by simp [powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (powList b L).length) :
    (powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [powList]

namespace PowTable

/-- The local variables of powTable: the arguments dst, L and b, the exponent j, and the power b^j.
-/
abbrev Dest : ℕ := 0
@[inherit_doc Dest] abbrev Len : ℕ := 1
@[inherit_doc Dest] abbrev Base : ℕ := 2
@[inherit_doc Dest] abbrev Expo : ℕ := 3
@[inherit_doc Dest] abbrev Power : ℕ := 4

end PowTable

open PowTable

/-- One round: dst[j] := p; p := p * b. -/
def powTableRound : Stmt :=
  .store (v Dest +' v Expo) (v Power) ;;
  .set Power (v Power *' v Base)

/-- powTable(dst, L, b): p := 1; for j < L: dst[j] := p; p := p * b. -/
def powTableBody : Stmt :=
  .set Power (k 1) ;;
  .for Expo (v Len) powTableRound

/-- The time of powTable. -/
def powTableTime (L : ℕ) : ℕ := 17 * L + 8

/-- The state before round j: p = b^j, the first j cells hold the powers up to b^(j-1), and no cell
outside the L cells from dst has changed.  The list t holds the local variables after the five of
powTable. -/
def PowTable.Filled (μ : ℕ → ℤ) (dst L b : ℕ) (t : List ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame (dst :: L :: b :: j :: ((b ^ j : ℕ) : ℤ) :: t), μ'⟩ ∧
    (∀ i < j, μ' (dst + i) = ((b ^ i : ℕ) : ℤ)) ∧ SameOutside μ μ' dst L

/-- The body of powTable writes the powers of b and changes nothing else, whatever its local
variables hold apart from the three arguments. -/
theorem powTable_ends {μ : ℕ → ℤ} {dst L b : ℕ} (e p : ℤ) (t : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d powTableBody ⟨frame (dst :: L :: b :: e :: p :: t), μ⟩ (powTableTime L) fun σ' =>
      Seg σ'.mem dst (powList b L) ∧ SameOutside μ σ'.mem dst L := by
  have : (1 : ℤ) ≤ lim.word := by simpa using hpow 0 (Nat.zero_le _)
  unfold powTableBody powTableTime
  -- p := 1
  light_set 1
  -- for j < L
  refine Ends.for (Filled μ dst L b t) L powTableRound.blockCost ?start ?round ?done ?bound
    (hT := by light_time [powTableRound])
  case start => exact ⟨μ, by simp [update_frame_setLocal], fun i hi => absurd hi (by omega), .refl⟩
  case bound =>
    rintro j _ - - ⟨μ', rfl, -⟩
    light_side
  case done =>
    rintro _ - ⟨μ', rfl, powers, same⟩
    exact ⟨fun i hi => by rw [getElem_powList]; exact powers i (by simpa using hi), same⟩
  case round =>
    rintro j _ hj - ⟨μ', rfl, powers, same⟩
    have : (b : ℤ) ^ (j + 1) ≤ lim.word := by exact_mod_cast hpow (j + 1) (by omega)
    have : 0 ≤ (b : ℤ) ^ (j + 1) := by positivity
    unfold powTableRound
    -- dst[j] := p
    light_store (dst + j) (b ^ j : ℕ)
    -- p := p * b
    light_set (b ^ (j + 1) : ℕ) using ← pow_succ
    refine ⟨by simp, Function.update μ' (dst + j) (b ^ j : ℕ), by simp [update_frame_setLocal],
      fun i hi => ?_, by light_keep⟩
    obtain hi | rfl := Nat.lt_succ_iff_lt_or_eq.1 hi
    · rw [Function.update_of_ne (by omega)]
      exact powers i hi
    · exact Function.update_self ..

end Light

namespace Light.Sec2

open ThreeSumApsp

/-! ## Sizes -/

/-- The parameters of the recursion and of the matrices: `L` levels, `m` of them inner, matrices
`N × D` and `D × N` with `D = 4^m`. -/
structure Par where
  /-- The number of levels of the recursion. -/
  L : ℕ
  /-- The number of inner levels. -/
  m : ℕ
  /-- The number of rows of `X` and of columns of `Y`. -/
  N : ℕ

namespace Par

/-- `D = 4^m`. -/
def D (p : Par) : ℕ := ThreeSumApsp.D p.m
/-- The number `L - m` of outer levels. -/
def Lo (p : Par) : ℕ := p.L - p.m
/-- `N₀ = 3^{L-m}`. -/
def N0 (p : Par) : ℕ := ThreeSumApsp.N0 p.L p.m
/-- `K = binom(L, m)`. -/
def K (p : Par) : ℕ := ThreeSumApsp.K p.L p.m
/-- `K₀ = ⌊√K⌋`. -/
def K0 (p : Par) : ℕ := ThreeSumApsp.K0 p.L p.m
/-- The number `K₀²` of subsets in the table. -/
def KK (p : Par) : ℕ := p.K0 * p.K0
/-- The number of row bands, and of column bands. -/
def nB (p : Par) : ℕ := numBands p.L p.m p.N
/-- The number `10^L` of leaves: the length of an encoding. -/
def T (p : Par) : ℕ := 10 ^ p.L
/-- The number `7^L` of left strings: the length of an input array. -/
def S7 (p : Par) : ℕ := 7 ^ p.L

/-! ## The shared block, from its base address `b0` on -/

/-- The directory: 32 cells, see `dirList`. -/
def aDIR (_p : Par) (b0 : ℕ) : ℕ := b0
/-- Powers of 3: `L + 1` cells. -/
def aP3 (_p : Par) (b0 : ℕ) : ℕ := b0 + 32
/-- Powers of 4: `L + 1` cells. -/
def aP4 (p : Par) (b0 : ℕ) : ℕ := p.aP3 b0 + (p.L + 1)
/-- Powers of 7: `L + 1` cells. -/
def aP7 (p : Par) (b0 : ℕ) : ℕ := p.aP4 b0 + (p.L + 1)
/-- Powers of 10: `L + 1` cells. -/
def aP10 (p : Par) (b0 : ℕ) : ℕ := p.aP7 b0 + (p.L + 1)
/-- Scratch for a row of Pascal's triangle: `L + 2` cells. -/
def aPAS (p : Par) (b0 : ℕ) : ℕ := p.aP10 b0 + (p.L + 1)
/-- The coefficients `φ_λ(s)`: 70 cells, row `λ` at `7 λ`. -/
def aPHI (p : Par) (b0 : ℕ) : ℕ := p.aPAS b0 + (p.L + 2)
/-- The coefficients `ψ_λ(t)`: 70 cells. -/
def aPSI (p : Par) (b0 : ℕ) : ℕ := p.aPHI b0 + 70
/-- The table of subsets: `K₀²` rows of `L` bits, the subset of the block product `(g, h)` in row
`g K₀ + h`. -/
def aMASK (p : Par) (b0 : ℕ) : ℕ := p.aPSI b0 + 70
/-- The band of every row: `N` cells. -/
def aBAND (p : Par) (b0 : ℕ) : ℕ := p.aMASK b0 + p.KK * p.L
/-- The block, within its band, of every row: `N` cells. -/
def aBLOCK (p : Par) (b0 : ℕ) : ℕ := p.aBAND b0 + p.N
/-- The base-3 digits of the offset of every row within its block: `N` rows of `L - m` cells, most
significant digit first. -/
def aDIG3 (p : Par) (b0 : ℕ) : ℕ := p.aBLOCK b0 + p.N
/-- The base-4 digits of every column of `X`: `D` rows of `m` cells, most significant digit first.
-/
def aDIG4 (p : Par) (b0 : ℕ) : ℕ := p.aDIG3 b0 + p.N * p.Lo
/-- The encodings of the row bands: band `β` at `β 10^L`. -/
def aENCA (p : Par) (b0 : ℕ) : ℕ := p.aDIG4 b0 + p.D * p.m
/-- The encodings of the column bands. -/
def aENCB (p : Par) (b0 : ℕ) : ℕ := p.aENCA b0 + p.nB * p.T
/-- The input array of the band that is being encoded: `7^L` cells.  Dead after the shared stage.
-/
def aARR (p : Par) (b0 : ℕ) : ℕ := p.aENCB b0 + p.nB * p.T
/-- Scratch of the recursive encoding: `7^L` cells (`7^{L-1} + … + 1` are used). Dead after the
shared stage. -/
def aZS (p : Par) (b0 : ℕ) : ℕ := p.aARR b0 + p.S7
/-- The first address after the shared block. -/
def sharedEnd (p : Par) (b0 : ℕ) : ℕ := p.aZS b0 + p.S7



end Par

def dirList (p : Par) (aX aY b0 : ℕ) : List ℕ :=
  [p.L, p.m, p.N, p.D, p.Lo, p.N0, p.K, p.K0, p.KK, p.nB, p.T, p.S7, aX, aY,
   p.aP3 b0, p.aP4 b0, p.aP7 b0, p.aP10 b0, p.aPAS b0, p.aPHI b0, p.aPSI b0, p.aMASK b0,
   p.aBAND b0, p.aBLOCK b0, p.aDIG3 b0, p.aDIG4 b0, p.aENCA b0, p.aENCB b0, p.aARR b0, p.aZS b0,
   p.sharedEnd b0]

/-! ## The places and the sizes, as equations and inequalities -/

/-- The places of the shared block: each area begins where the one before it ends. -/
theorem Par.places (p : Par) (b0 : ℕ) :
    p.aDIR b0 = b0 ∧ p.aP3 b0 = b0 + 32 ∧ p.aP4 b0 = p.aP3 b0 + (p.L + 1)
      ∧ p.aP7 b0 = p.aP4 b0 + (p.L + 1)
      ∧ p.aP10 b0 = p.aP7 b0 + (p.L + 1) ∧ p.aPAS b0 = p.aP10 b0 + (p.L + 1)
      ∧ p.aPHI b0 = p.aPAS b0 + (p.L + 2) ∧ p.aPSI b0 = p.aPHI b0 + 70
      ∧ p.aMASK b0 = p.aPSI b0 + 70 ∧ p.aBAND b0 = p.aMASK b0 + p.KK * p.L
      ∧ p.aBLOCK b0 = p.aBAND b0 + p.N ∧ p.aDIG3 b0 = p.aBLOCK b0 + p.N
      ∧ p.aDIG4 b0 = p.aDIG3 b0 + p.N * p.Lo ∧ p.aENCA b0 = p.aDIG4 b0 + p.D * p.m
      ∧ p.aENCB b0 = p.aENCA b0 + p.nB * p.T ∧ p.aARR b0 = p.aENCB b0 + p.nB * p.T
      ∧ p.aZS b0 = p.aARR b0 + p.S7 ∧ p.sharedEnd b0 = p.aZS b0 + p.S7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Par
variable (p : Par)

theorem one_le_T : 1 ≤ p.T := Nat.one_le_pow _ _ (by omega)

theorem L_lt_T : p.L < p.T := Nat.lt_pow_self (by omega)

/-- `2^L ≤ 10^L`. -/
theorem two_pow_le_T : 2 ^ p.L ≤ p.T := Nat.pow_le_pow_left (by omega) _

theorem K_le_T : p.K ≤ p.T := (Nat.choose_le_two_pow _ _).trans p.two_pow_le_T

theorem N0_le_T : p.N0 ≤ p.T :=
  (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))

theorem D_le_T (hmL : p.m ≤ p.L) : p.D ≤ p.T :=
  (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) hmL)

theorem K0_le_K : p.K0 ≤ p.K := Nat.sqrt_le_self _

/-- `K₀² ≤ K`. -/
theorem KK_le_K : p.KK ≤ p.K := Nat.sqrt_le _

/-- The sizes: 1, `L`, `2^L`, `K`, `N₀` and `D` are at most `T = 10^L`; `K₀` and `K₀²` are at most
`K`; `K₀` and `N₀` are positive; and the definition of `Lo`. -/
theorem sizes (hmL : p.m ≤ p.L) :
    1 ≤ p.T ∧ p.L < p.T ∧ 2 ^ p.L ≤ p.T ∧ p.K ≤ p.T ∧ p.N0 ≤ p.T ∧ p.D ≤ p.T ∧ p.K0 ≤ p.K
      ∧ p.KK ≤ p.K ∧ 0 < p.K0 ∧ 0 < p.N0 ∧ p.Lo = p.L - p.m :=
  ⟨p.one_le_T, p.L_lt_T, p.two_pow_le_T, p.K_le_T, p.N0_le_T, p.D_le_T hmL, p.K0_le_K, p.KK_le_K,
    ThreeSumApsp.K0_pos hmL, ThreeSumApsp.N0_pos _ _, rfl⟩

end Par




/-! ## Vocabulary -/

/-- The cells from a on hold a list of bits, as 1 and 0. -/
def SegB (μ : ℕ → ℤ) (a : ℕ) (l : List Bool) : Prop :=
  Seg μ a (l.map fun b : Bool => if b then (1 : ℤ) else 0)

/-- A cell of a segment of bits. -/
theorem SegB.get {μ : ℕ → ℤ} {a : ℕ} {l : List Bool} (h : SegB μ a l) {q : ℕ} (hq : q < l.length) :
    μ (a + q) = if l.getD q false then 1 else 0 :=
  (Seg.getD h (by rwa [List.length_map]) 0).trans (List.getD_map_of_lt _ hq false 0)

/-! ## The numbers of the procedures

Number 0 is empty.  1 to 25: the shared routines and those of Theorem 5.  26 to 28: the test of the
regime, the brute force, and the solver for all instances.  29 to 39 are not used.  From 40 on:
Section 4. -/

/-- The number of pow. -/
def pPow : ℕ := 2
/-- The number of binom. -/
def pBinom : ℕ := 3
/-- The number of sqrt. -/
def pSqrt : ℕ := 4
/-- The number of subsets. -/
def pSubsets : ℕ := 5
/-- The number of counters. -/
def pCounters : ℕ := 6
/-- The number of digits. -/
def pDigits : ℕ := 7
/-- The number of coef. -/
def pCoef : ℕ := 8
/-- The number of bandArray. -/
def pBandArray : ℕ := 9
/-- The number of encStep. -/
def pEncStep : ℕ := 10
/-- The number of the brute force. -/
def pThinBrute : ℕ := 27

/-! ## The entries of the shared routines -/

section Entries

variable (lim : Limits) (P : Program) (c : ℕ)

/-- pow(b, n, dst): writes b^0, …, b^n to dst. -/
def PowSpec : Prop :=
  ∀ (b n dst : ℕ) (μ : ℕ → ℤ),
    1 ≤ dst → dst + (n + 1) ≤ lim.space → 1 ≤ b →
    ((b ^ (n + 1) : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pPow d [b, n, dst] μ (c * (n + 1)) fun _ μ' =>
      Seg μ' dst (powList b (n + 1)) ∧ SameOutside μ μ' dst (n + 1)

/-- binom(L, m, pas): returns binom(L, m), by Pascal's triangle in the L + 2 cells from pas. -/
def BinomSpec : Prop :=
  ∀ (L m pas : ℕ) (μ : ℕ → ℤ),
    pas + (L + 2) ≤ lim.space → m ≤ L → ((2 ^ L : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pBinom d [L, m, pas] μ (c * (L + 1) ^ 2) fun r μ' =>
      r = (L.choose m : ℕ) ∧ SameOutside μ μ' pas (L + 2)

/-- sqrt(K): returns ⌊√K⌋, by counting up.  Changes no cell. -/
def SqrtSpec : Prop :=
  ∀ (K : ℕ) (μ : ℕ → ℤ),
    ((4 * K + 4 : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pSqrt d [K] μ (c * (Nat.sqrt K + 1)) fun r μ' =>
      r = (Nat.sqrt K : ℕ) ∧ μ' = μ

/-- subsets(L, m, KK, mask): writes the first KK subsets of size m of the L levels, as rows of L
bits, in the order of Spec.unrank. -/
def SubsetsSpec : Prop :=
  ∀ (L m KK mask : ℕ) (μ : ℕ → ℤ),
    mask + KK * L ≤ lim.space → m ≤ L → KK ≤ L.choose m →
    ((KK + L : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P pSubsets d [L, m, KK, mask] μ (c * ((KK + 1) * (L + 1))) fun _ μ' =>
      (∀ s < KK, SegB μ' (mask + s * L) (Spec.unrank L m s)) ∧ SameOutside μ μ' mask (KK * L)

/-- counters(N, K0, N0, band): for every row I < N writes its band I / (K0 N0) to band + I and its
block I / N0 % K0 to band + N + I, by counting. -/
def CountersSpec : Prop :=
  ∀ (N K0 N0 band : ℕ) (μ : ℕ → ℤ),
    band + 2 * N ≤ lim.space → 0 < K0 → 0 < N0 →
    ((K0 + N0 : ℕ) : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P pCounters d [N, K0, N0, band] μ (c * (N + 1)) fun _ μ' =>
      (∀ I < N, μ' (band + I) = (I / (K0 * N0) : ℕ) ∧ μ' (band + N + I) = (I / N0 % K0 : ℕ))
      ∧ SameOutside μ μ' band (2 * N)

/-- digits(n, b, len, dst): for every x < n writes the len digits of x % b^len in base b, most
significant first, to dst + x len, by an odometer. -/
def DigitsSpec : Prop :=
  ∀ (n b len dst : ℕ) (μ : ℕ → ℤ),
    dst + n * len ≤ lim.space → 2 ≤ b → (b : ℤ) ≤ lim.word →
    (n : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P pDigits d [n, b, len, dst] μ (c * ((n + 1) * (len + 1))) fun _ μ' =>
      (∀ x < n, SegN μ' (dst + x * len) (ThreeSumApsp.digitList b len (x % b ^ len)))
      ∧ SameOutside μ μ' dst (n * len)

/-- coef(phi): writes the 70 coefficients φ_λ(s) to phi and the 70 coefficients ψ_λ(t) to phi + 70.
-/
def CoefSpec : Prop :=
  ∀ (phi : ℕ) (μ : ℕ → ℤ),
    phi + 140 ≤ lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P pCoef d [phi] μ c fun _ μ' =>
      Seg μ' phi Spec.phiFlat ∧ Seg μ' (phi + 70) Spec.psiFlat
      ∧ SameOutside μ μ' phi 140

/-- What bandArray reads, apart from the matrix: the table of subsets and the two tables of digits,
all below the array it writes. -/
structure BandTables (p : Par) (μ : ℕ → ℤ) (mask dig3 dig4 arr : ℕ) : Prop where
  hmask : ∀ s < p.KK, SegB μ (mask + s * p.L) (Spec.unrank p.L p.m s)
  hdig3 : ∀ I < p.N, SegN μ (dig3 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % p.N0))
  hdig4 : ∀ x < p.D, SegN μ (dig4 + x * p.m) (ThreeSumApsp.digitList 4 p.m x)
  mask_le : mask + p.KK * p.L ≤ arr
  dig3_le : dig3 + p.N * p.Lo ≤ arr
  dig4_le : dig4 + p.D * p.m ≤ arr

/-- The shape of the running time of bandArray: clear 7^L cells, then one entry in O(L) steps for
each subset of the table, each row of a block and each column. -/
def bandArrayShape (p : Par) : ℕ := p.S7 + (p.KK * p.N0 * p.D + 1) * (p.L + 1)

/-- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr), for the left
side: side = 0, aA the address of X, sI = D, sK = 1 (sI and sK are the strides of the index I of the
band and of the inner index k: the entry is at aA + I sI + k sK).  Writes the input array of the row
band β (Section 2.3.4), in the order of the codes, to arr. -/
def BandArrayLSpec : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (β aX mask dig3 dig4 arr : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ),
    arr + p.S7 ≤ lim.space → MatAt μ aX X → aX + p.N * p.D ≤ arr →
    BandTables p μ mask dig3 dig4 arr → β < p.nB →
    ∀ d, d ≤ lim.depth → Meets lim P pBandArray d
      [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, 0, aX, p.D, 1, mask, dig3, dig4, arr] μ
      (c * bandArrayShape p) fun _ μ' =>
      Seg μ' arr (Spec.arrL (bandArrayL (Spec.stdLayout hmL) X β)) ∧ SameOutside μ μ' arr p.S7

/-- The same procedure for the right side: side = 1, aA the address of Y, sI = 1, sK = N. Writes the
input array of the column band β. -/
def BandArrayRSpec : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (β aY mask dig3 dig4 arr : ℕ) (μ : ℕ → ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ),
    arr + p.S7 ≤ lim.space → MatAt μ aY Y → aY + p.D * p.N ≤ arr →
    BandTables p μ mask dig3 dig4 arr → β < p.nB →
    ∀ d, d ≤ lim.depth → Meets lim P pBandArray d
      [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, 1, aY, 1, p.N, mask, dig3, dig4, arr] μ
      (c * bandArrayShape p) fun _ μ' =>
      Seg μ' arr (Spec.arrR (bandArrayR (Spec.stdLayout hmL) Y β)) ∧ SameOutside μ μ' arr p.S7

/-- Where encode finds its tables and its areas: the tables lie below dst, the 10^n cells of dst
below src, the 7^n cells of src below scr, and scr has 7^n cells. -/
structure EncodePlaces (n Lmax src dst scr tab p7 p10 : ℕ) (μ : ℕ → ℤ) : Prop where
  n_le : n ≤ Lmax
  hp7 : Seg μ p7 (powList 7 (Lmax + 1))
  hp10 : Seg μ p10 (powList 10 (Lmax + 1))
  tab_le : tab + 70 ≤ dst
  p7_le : p7 + (Lmax + 1) ≤ dst
  p10_le : p10 + (Lmax + 1) ≤ dst
  dst_le : dst + 10 ^ n ≤ src
  src_le : src + 7 ^ n ≤ scr
  scr_le : scr + 7 ^ n ≤ lim.space

/-! ## The shared stage -/

/-- The tables of the powers of 3, 4, 7 and 10 in the shared block. -/
structure PowTables (p : Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop where
  p3 : Seg μ (p.aP3 b0) (powList 3 (p.L + 1))
  p4 : Seg μ (p.aP4 b0) (powList 4 (p.L + 1))
  p7 : Seg μ (p.aP7 b0) (powList 7 (p.L + 1))
  p10 : Seg μ (p.aP10 b0) (powList 10 (p.L + 1))

/-- The other tables of the shared block: the coefficients, the subsets, the band and the block of
every row, and the digits of the offsets and of the inner indices. -/
structure RowTables (p : Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop where
  phi : Seg μ (p.aPHI b0) Spec.phiFlat
  psi : Seg μ (p.aPSI b0) Spec.psiFlat
  mask : ∀ s < p.KK, SegB μ (p.aMASK b0 + s * p.L) (Spec.unrank p.L p.m s)
  band : ∀ I < p.N, μ (p.aBAND b0 + I) = (I / (p.K0 * p.N0) : ℕ)
  block : ∀ I < p.N, μ (p.aBLOCK b0 + I) = (I / p.N0 % p.K0 : ℕ)
  dig3 : ∀ I < p.N, SegN μ (p.aDIG3 b0 + I * p.Lo) (ThreeSumApsp.digitList 3 p.Lo (I % p.N0))
  dig4 : ∀ x < p.D, SegN μ (p.aDIG4 b0 + x * p.m) (ThreeSumApsp.digitList 4 p.m x)

/-- The tables of the shared block, all in one memory. -/
structure SharedTables (p : Par) (b0 : ℕ) (μ : ℕ → ℤ) : Prop
  extends PowTables p b0 μ, RowTables p b0 μ

/-- The shape of the running time of the shared stage. -/
def sharedShape (p : Par) : ℕ :=
  (p.L + 1) ^ 2 + (Nat.sqrt p.K + 1) + (p.KK + 1) * (p.L + 1) + (p.N + 1) * (p.Lo + 1)
    + (p.D + 1) * (p.m + 1)
    + p.nB * (p.T + bandArrayShape p)

/-- What the shared stage assumes: the shared block fits in the memory, X and Y stand below it, V
bounds their entries, and the encoded numbers and the powers of ten fit in a word. -/
structure SharedPre (p : Par) (aX aY b0 : ℕ) (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ) (μ : ℕ → ℤ) : Prop where
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

namespace SortWanted

end SortWanted

end Entries




/-! ## The directory -/

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-! ## Only the shared block matters -/

/-- The tables lie between the directory and the encodings: they are still there in a memory that
agrees on these cells. -/
theorem SharedTables.congr {p : Par} {b0 : ℕ} {μ μ' : ℕ → ℤ} (h : SharedTables p b0 μ)
    (he : ∀ x, p.aP3 b0 ≤ x → x < p.aENCA b0 → μ' x = μ x) : SharedTables p b0 μ' := by
  have := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  have := Spec.length_phiFlat
  have := Spec.length_psiFlat
  refine
    { p3 := h.p3.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p4 := h.p4.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p7 := h.p7.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      p10 := h.p10.congr fun i hi => he _ (by omega) (by rw [lp] at hi; omega)
      phi := h.phi.congr fun i hi => he _ (by omega) (by omega)
      psi := h.psi.congr fun i hi => he _ (by omega) (by omega)
      mask := fun s hs => (h.mask s hs).congr fun i hi => he _ (by omega) ?_
      band := fun I hI => (he _ (by omega) (by omega)).trans (h.band I hI)
      block := fun I hI => (he _ (by omega) (by omega)).trans (h.block I hI)
      dig3 := fun I hI => (h.dig3 I hI).congr fun i hi => he _ (by omega) ?_
      dig4 := fun x hx => (h.dig4 x hx).congr fun i hi => he _ (by omega) ?_ }
  · rw [List.length_map, Spec.length_unrank] at hi
    have := Nat.mul_add_lt_mul hs hi
    omega
  · have := Nat.mul_add_lt_mul hI (show i < p.Lo by simpa [ThreeSumApsp.digitList] using hi)
    omega
  · have := Nat.mul_add_lt_mul hx (show i < p.m by simpa [ThreeSumApsp.digitList] using hi)
    omega

end Light.Sec2
