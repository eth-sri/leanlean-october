/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Programs.Sec2.Theorem5.CellDependencies
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.AllBands

/-!
# The shared stage: everything up to the encodings of all bands

shared(L, m, N, D, aX, aY, b0) fills the shared block of the memory map: the tables of powers, the
coefficients φ and ψ of Schönhage's identity (Section 2.2), the table of the K₀² subsets (Section
2.3.4), band, block and digits of every row, the digits of every column, the encodings of all row
bands of X and of all column bands of Y (Section 2.4.1), and the directory. Theorem 5 and the data
structure of Section 4 both start with it.

The shared stage fills tables from low to high addresses. The pruned implementation verifies
these two parts together with the final encoder in `sharedP_entry`.
The places of the areas are those of `Par.places`, and their sizes those of `Par.sizes`.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

/-! ## The local variables -/

namespace Shared

/-- Local 0 of shared: L. -/
registers [
  Levels,
  /- Local 1 of shared: m. -/ Inner,
  /- Local 2 of shared: N. -/ Rows,
  /- Local 3 of shared: D. -/ Cols,
  /- Local 4 of shared: the address of X. -/ AdrX,
  /- Local 5 of shared: the address of Y. -/ AdrY,
  /- Local 6 of shared: the base address b0 of the block. -/ Base,
  /- Local 7 of shared: the address of the powers of 3. -/ AdrP3,
  /- Local 8 of shared: the address of the powers of 4. -/ AdrP4,
  /- Local 9 of shared: the address of the powers of 7. -/ AdrP7,
  /- Local 10 of shared: the address of the powers of 10. -/ AdrP10,
  /- Local 11 of shared: the address of the scratch row of Pascal's triangle. -/ AdrPas,
  /- Local 12 of shared: the address of the coefficients φ. -/ AdrPhi,
  /- Local 13 of shared: the address of the coefficients ψ. -/ AdrPsi,
  /- Local 14 of shared: the address of the table of subsets. -/ AdrMask,
  /- Local 15 of shared: the address of the bands of the rows. -/ AdrBand,
  /- Local 16 of shared: the address of the blocks of the rows. -/ AdrBlock,
  /- Local 17 of shared: the address of the base-3 digits. -/ AdrDig3,
  /- Local 18 of shared: the address of the base-4 digits. -/ AdrDig4,
  /- Local 19 of shared: the address of the encodings of the row bands. -/ AdrEncA,
  /- Local 20 of shared: the address of the encodings of the column bands. -/ AdrEncB,
  /- Local 21 of shared: the address of the input array of a band. -/ AdrArr,
  /- Local 22 of shared: the address of the scratch array of encode. -/ AdrZs,
  /- Local 23 of shared: the end of the block. -/ AdrEnd,
  /- Local 24 of shared: L - m. -/ Outer,
  /- Local 25 of shared: N₀. -/ BlockRows,
  /- Local 26 of shared: K. -/ Subsets,
  /- Local 27 of shared: K₀. -/ Root,
  /- Local 28 of shared: K₀². -/ Table,
  /- Local 29 of shared: the number of bands. -/ Bands,
  /- Local 30 of shared: 10^L. -/ Leaves,
  /- Local 31 of shared: 7^L. -/ Strings,
  /- Local 32 of shared: takes the results of calls that return nothing. -/ Void]

end Shared

open Shared

/-! ## The text -/

/-- Stores the locals of the list xs into the cells from b0 + i on. -/
def storeLocals : ℕ → List ℕ → Stmt
  | _, [] => .skip
  | i, x :: xs => .store (v Base +' k i) (v x) ;; storeLocals (i + 1) xs

/-- **storeLocals** writes the values of the locals to the cells from base + i on, changes nothing
else, and takes 5 steps for each. -/
theorem storeLocals_spec {d : ℕ} (hw : (lim.space : ℤ) ≤ lim.word) {base : ℕ} (loc : ℕ → ℤ)
    (hbase : loc Base = base) (xs : List ℕ) :
    ∀ (i : ℕ) (μ : ℕ → ℤ), base + i + xs.length ≤ lim.space →
      Ends lim P d (storeLocals i xs) ⟨loc, μ⟩ (5 * xs.length) fun σ' =>
        Seg σ'.mem (base + i) (xs.map loc) ∧ SameOutside μ σ'.mem (base + i) xs.length := by
  induction xs with
  | nil => exact fun i μ _ => Ends.skip ⟨Seg.nil, SameOutside.refl⟩
  | cons x xs ih =>
    intro i μ hsp
    rw [List.length_cons] at hsp ⊢
    have haddr : ((v Base +' k i).val ⟨loc, μ⟩).toNat = base + i := by simp [hbase]
    -- mem[base + i] := x
    refine Ends.storeThen ?_ (by light_side [hbase])
    rw [haddr]
    refine (ih (i + 1) _ (by omega)).mono (by simp; omega) ?_
    rintro σ' ⟨hs, hf⟩
    refine ⟨seg_cons.2 ⟨?_, by rw [Nat.add_assoc]; exact hs⟩, fun b hb => ?_⟩
    · rw [hf (base + i) (Or.inl (by omega)), Function.update_self]
      rfl
    · rw [hf b (by omega), Function.update_of_ne (by omega)]

/-- The first part of shared: the addresses of the first areas, the four tables of powers, and
L - m, N₀, 10^L, 7^L. -/
def sharedA : Stmt :=
  .set AdrP3 (v Base +' k 32) ;;
  .set AdrP4 (v AdrP3 +' (v Levels +' k 1)) ;;
  .set AdrP7 (v AdrP4 +' (v Levels +' k 1)) ;;
  .set AdrP10 (v AdrP7 +' (v Levels +' k 1)) ;;
  .set AdrPas (v AdrP10 +' (v Levels +' k 1)) ;;
  .set AdrPhi (v AdrPas +' (v Levels +' k 2)) ;;
  .set AdrPsi (v AdrPhi +' k 70) ;;
  .set AdrMask (v AdrPsi +' k 70) ;;
  .call pPow [k 3, v Levels, v AdrP3] Void ;;
  .call pPow [k 4, v Levels, v AdrP4] Void ;;
  .call pPow [k 7, v Levels, v AdrP7] Void ;;
  .call pPow [k 10, v Levels, v AdrP10] Void ;;
  .set Outer (v Levels -' v Inner) ;;
  .set BlockRows (M (v AdrP3 +' v Outer)) ;;
  .set Leaves (M (v AdrP10 +' v Levels)) ;;
  .set Strings (M (v AdrP7 +' v Levels)) ;;
  .skip

/-- The second part of shared: K, K₀, K₀², the coefficients, the table of subsets, band, block and
digits of every row, the digits of every column. -/
def sharedB : Stmt :=
  .call pBinom [v Levels, v Inner, v AdrPas] Subsets ;;
  .call pSqrt [v Subsets] Root ;;
  .set Table (v Root *' v Root) ;;
  .call pCoef [v AdrPhi] Void ;;
  .call pSubsets [v Levels, v Inner, v Table, v AdrMask] Void ;;
  .set AdrBand (v AdrMask +' v Table *' v Levels) ;;
  .set AdrBlock (v AdrBand +' v Rows) ;;
  .set AdrDig3 (v AdrBlock +' v Rows) ;;
  .call pCounters [v Rows, v Root, v BlockRows, v AdrBand] Void ;;
  .call pDigits [v Rows, k 3, v Outer, v AdrDig3] Void ;;
  .set AdrDig4 (v AdrDig3 +' v Rows *' v Outer) ;;
  .call pDigits [v Cols, k 4, v Inner, v AdrDig4] Void ;;
  .set AdrEncA (v AdrDig4 +' v Cols *' v Inner) ;;
  .skip

/-- The number of bands: 0 if there is no row, and else one more than the band of the last row. -/
def sharedBands : Stmt :=
  .ite (v Rows =' k 0) (.set Bands (k 0)) (.set Bands (M (v AdrBand +' (v Rows -' k 1)) +' k 1))

/-- The time of the first part, if every callee meets its entry with the constant c. -/
def sharedTimeA (c : ℕ) (p : Par) : ℕ := 4 * (c * (p.L + 1)) + 81

/-- The time of the second part. -/
def sharedTimeB (c : ℕ) (p : Par) : ℕ :=
  c * (p.L + 1) ^ 2 + c * (Nat.sqrt p.K + 1) + c + c * ((p.KK + 1) * (p.L + 1)) + c * (p.N + 1)
    + c * ((p.N + 1) * (p.Lo + 1)) + c * ((p.D + 1) * (p.m + 1)) + 65

/-- The original arguments, used by all three parts. -/
abbrev sharedArgs (p : Par) (aX aY b0 : ℕ) : List ℤ := [p.L, p.m, p.N, p.D, aX, aY, b0]

abbrev sharedPrefix (p : Par) (aX aY b0 : ℕ) : List ℤ :=
  sharedArgs p aX aY b0 ++
    ([p.aP3 b0, p.aP4 b0, p.aP7 b0, p.aP10 b0, p.aPAS b0, p.aPHI b0, p.aPSI b0, p.aMASK b0] : List ℤ)

/-- The locals after the second part. -/
def sharedLocB (p : Par) (aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  sharedPrefix p aX aY b0 ++
    ([p.aBAND b0, p.aBLOCK b0, p.aDIG3 b0, p.aDIG4 b0, p.aENCA b0, 0, 0, 0, 0,
      p.Lo, p.N0, p.K, p.K0, p.KK, 0, p.T, p.S7, r] : List ℤ)

/-- The entries of the routines that the shared stage calls, with their constants. -/
structure SharedCallees (lim : Limits) (P : Program) (c : ℕ) : Prop where
  pow : PowSpec lim P c
  binom : BinomSpec lim P c
  sqrt : SqrtSpec lim P c
  coef : CoefSpec lim P c
  subsets : SubsetsSpec lim P c
  counters : CountersSpec lim P c
  digits : DigitsSpec lim P c

/-- The assumption on the word size, in terms of `T = 10^L`. -/
theorem Par.ten_T_le {p : Par} (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word) :
    10 * (p.T : ℤ) ≤ lim.word := by
  rw [pow_succ, Nat.mul_comm] at h10
  exact_mod_cast h10

/-- The entry of pow, for a table of the powers b^0, …, b^L of a base b ≤ 10. -/
theorem SharedCallees.powTable {c : ℕ} (C : SharedCallees lim P c) {p : Par}
    (h10 : ((10 ^ (p.L + 1) : ℕ) : ℤ) ≤ lim.word) (b dst : ℕ) (μ : ℕ → ℤ)
    (one_le : 1 ≤ b := by omega) (le_ten : b ≤ 10 := by omega) (dst_pos : 1 ≤ dst := by omega)
    (dst_le : dst + (p.L + 1) ≤ lim.space := by omega) :
    ∀ d, d ≤ lim.depth → Meets lim P pPow d [b, p.L, dst] μ (c * (p.L + 1)) fun _ μ' =>
      Seg μ' dst (powList b (p.L + 1)) ∧ SameOutside μ μ' dst (p.L + 1) :=
  C.pow b p.L dst μ dst_pos dst_le one_le
    (le_trans (by gcongr <;> omega) h10)

/-- What bandArray reads of the tables. -/
theorem SharedTables.bandTables {p : Par} {b0 : ℕ} {μ : ℕ → ℤ} (h : SharedTables p b0 μ) :
    BandTables p μ (p.aMASK b0) (p.aDIG3 b0) (p.aDIG4 b0) (p.aENCA b0) := by
  have hplaces := p.places b0
  exact ⟨h.mask, h.dig3, h.dig4, by omega, by omega, by omega⟩

/-- The addresses that the shared stage hands to encodeBands: the coefficients stand at tab, and the
encodings are written from enc on. -/
@[simp] def Par.bandsArgs (p : Par) (b0 tab enc : ℕ) : BandsArgs where
  mask := p.aMASK b0
  dig3 := p.aDIG3 b0
  dig4 := p.aDIG4 b0
  arr := p.aARR b0
  zs := p.aZS b0
  tab := tab
  p7 := p.aP7 b0
  p10 := p.aP10 b0
  enc := enc

/-- What encodeBands assumes holds once the tables are there, for either of the two areas enc of
encodings. -/
theorem SharedTables.bandsPre {p : Par} {b0 tab enc : ℕ} {μ : ℕ → ℤ} {coefs : List ℤ} {V : ℤ}
    (h : SharedTables p b0 μ) (hsp : p.sharedEnd b0 ≤ lim.space) (hV0 : 0 ≤ V)
    (hVB : 7 ^ (p.L + 1) * V ≤ lim.word) (coef : Seg μ tab coefs) (coef_le : tab + 70 ≤ enc)
    (le_enc : p.aENCA b0 ≤ enc) (enc_le : enc + p.nB * p.T ≤ p.aARR b0) :
    BandsPre lim p μ (p.bandsArgs b0 tab enc) coefs V := by
  have hplaces := p.places b0
  exact
    { tables := h.bandTables.mono le_enc
      coef := coef
      coef_le := coef_le
      p7 := h.p7
      p7_le := show p.aP7 b0 + (p.L + 1) ≤ enc by omega
      p10 := h.p10
      p10_le := show p.aP10 b0 + (p.L + 1) ≤ enc by omega
      enc_le := enc_le
      arr_le := show p.aARR b0 + p.S7 ≤ p.aZS b0 by omega
      zs_le := show p.aZS b0 + p.S7 ≤ lim.space by omega
      V_nonneg := hV0
      word := hVB }

/-- The number of bands, from the band of the last row. -/
theorem nB_eq (p : Par) (hmL : p.m ≤ p.L) :
    (p.N = 0 → p.nB = 0) ∧ (0 < p.N → p.nB = (p.N - 1) / (p.K0 * p.N0) + 1) := by
  have hb : 0 < p.K0 * p.N0 := Nat.mul_pos (K0_pos hmL) (N0_pos _ _)
  have e : p.nB = (p.N + p.K0 * p.N0 - 1) / (p.K0 * p.N0) := rfl
  constructor
  · intro h
    rw [e, h, Nat.zero_add]
    exact Nat.div_eq_of_lt (by omega)
  · intro h
    rw [e, ← Nat.add_div_right _ hb]
    congr 1
    omega

/-- **The number of bands**: 0 if there is no row, and else one more than the band of the last
row. -/
theorem sharedBands_spec (std : Std lim) {d : ℕ} {p : Par} (hmL : p.m ≤ p.L) {aX aY b0 : ℕ}
    (hsp : p.sharedEnd b0 ≤ lim.space) (μ : ℕ → ℤ) (r0 : ℤ) (tb : SharedTables p b0 μ) :
    Ends lim P d sharedBands ⟨frame (sharedLocB p aX aY b0 r0), μ⟩ 13 fun σ' =>
      σ' = ⟨frame (setLocal (sharedLocB p aX aY b0 r0) Bands (p.nB : ℕ)), μ⟩ := by
  light_facts std
  have hplaces := p.places b0
  obtain ⟨hnB0, hnB1⟩ := nB_eq p hmL
  unfold sharedBands sharedLocB
  refine Ends.iteLast (fun hN => ?_) (fun hN => ?_)
  · -- nB := 0
    have hNzero : p.N = 0 := by simpa using hN
    exact Ends.setTo (p.nB : ℕ) rfl (by simp [hnB0 hNzero]; omega)
  · -- nB := mem[BAND + (N - 1)] + 1
    have hNpos : 0 < p.N := Nat.pos_of_ne_zero (by simpa using hN)
    have hlast := tb.band (p.N - 1) (by omega)
    have haddr : ((p.aBAND b0 : ℤ) + ((p.N : ℤ) - 1)).toNat = p.aBAND b0 + (p.N - 1) := by omega
    have hle : (p.N - 1) / (p.K0 * p.N0) ≤ p.N := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    have hnB := hnB1 hNpos
    generalize (p.N - 1) / (p.K0 * p.N0) = q at hlast hle hnB
    exact Ends.setTo (p.nB : ℕ) rfl (by light_side [haddr, hlast, hnB])

end Light.Sec2
