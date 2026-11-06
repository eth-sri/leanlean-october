/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Theorem5.WordSize

/-!
# The encodings of all bands of one matrix (Section 2.4.1)

Section 2.4.1: "We compute the encodings of the input arrays of all row bands and all column bands
[...], and every tile reads its two encodings from these."  encodeBands does this for one of the two
matrices: for each band β it calls bandArray, which forms the input array of the band at arr, and
encode, which leaves its encoding in the T = 10^L cells from enc + β T.

The loop is treated once, for callees that are described by what they do here (`encodeBands_proc`).
The two entries, for the row bands of X and for the column bands of Y, put in the specifications of
bandArray and encode for their side.
-/

@[expose] public section

namespace Light.Sec2



variable {lim : Limits} {P : Program}


/-! ## The arguments, and what is assumed about them -/

/-- The addresses that encodeBands gets besides that of the matrix.  mask, dig3 and dig4 are the
tables that bandArray reads, tab, p7 and p10 those that encode reads.  arr and zs are scratch, and
the encodings are written from enc on. -/
structure BandsArgs where
  (mask dig3 dig4 arr zs tab p7 p10 enc : ℕ)

/-- The arguments of encodeBands at the sizes of p, for the matrix at aA with the strides sI and
sK. -/
@[simp] def BandsArgs.vals (x : BandsArgs) (p : Par) (side aA sI sK : ℕ) : List ℤ :=
  [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, side, aA, sI, sK, x.mask, x.dig3, x.dig4,
    x.arr, x.zs, x.tab, x.p7, x.p10, x.enc]

/-- What encodeBands assumes besides the matrix.  Everything that is read lies below enc: the tables
of bandArray, the 70 coefficients coefs of the side, and the powers of 7 and of 10.  From enc on
follow the encodings and the two scratch areas.  V bounds the entries of the matrix. -/
structure BandsPre (lim : Limits) (p : Par) (μ : Light.Memory) (x : BandsArgs) (coefs : List ℤ) (V : ℤ) :
    Prop where
  tables : BandTables p μ x.mask x.dig3 x.dig4 x.enc
  coef : Seg μ x.tab coefs
  coef_le : x.tab + 70 ≤ x.enc
  p7 : Seg μ x.p7 (powList 7 (p.L + 1))
  p7_le : x.p7 + p.L + 1 ≤ x.enc
  p10 : Seg μ x.p10 (powList 10 (p.L + 1))
  p10_le : x.p10 + p.L + 1 ≤ x.enc
  enc_le : x.enc + p.nB * p.T ≤ x.arr
  arr_le : x.arr + p.S7 ≤ x.zs
  zs_le : x.zs + p.S7 ≤ lim.space
  V_nonneg : 0 ≤ V
  word : 7 ^ (p.L + 1) * V ≤ lim.word

variable {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ μ' : Light.Memory}

/-! ## What is read does not change -/

/-- The tables that bandArray reads, in a memory that agrees below their bound. -/
theorem BandTables.congr_below {p} {μ μ'} {mask dig3 dig4 e}
    (h : BandTables p μ mask dig3 dig4 e) (hlow : ∀ x < e, μ' x = μ x) :
    BandTables p μ' mask dig3 dig4 e where
  hmask := fun s hs => (h.hmask s hs).congr fun i hi => hlow _ (by
    ram_safe)
  hdig3 := fun I hI => (h.hdig3 I hI).congr fun i hi => hlow _ (by
    ram_safe)
  hdig4 := fun x hx => (h.hdig4 x hx).congr fun i hi => hlow _ (by
    ram_safe)
  mask_le := h.mask_le
  dig3_le := h.dig3_le
  dig4_le := h.dig4_le

/-- The tables also lie below every larger bound. -/
def BandTables.mono {p} {μ} {mask dig3 dig4 e e'}
    (h : BandTables p μ mask dig3 dig4 e) (hle : e ≤ e') :=
  { h with
    mask_le := h.mask_le.trans hle
    dig3_le := h.dig3_le.trans hle
    dig4_le := h.dig4_le.trans hle }

/-- The places of the call of encode for the band β, in a memory that agrees with μ below enc. -/
theorem BandsPre.encodePlaces (pre : BandsPre lim p μ x coefs V) {β} (hβ : β < p.nB)
    (hlow : ∀ b < x.enc, μ' b = μ b) :
    EncodePlaces lim p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 μ' := by
  light_facts pre
  exact
    { n_le := le_rfl
      hp7 := pre.p7.congr fun i hi => hlow _ (by simp at hi; omega)
      hp10 := pre.p10.congr fun i hi => hlow _ (by simp at hi; omega)
      tab_le := by omega
      p7_le := by omega
      p10_le := by omega
      dst_le := by
        have  : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
        change x.enc + β * p.T + p.T ≤ x.arr
        omega
      src_le := pre.arr_le
      scr_le := pre.zs_le }

/-! ## The two entries -/

end Light.Sec2
