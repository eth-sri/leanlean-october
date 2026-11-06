/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.ToMachine
public import ThreeSumApsp.Programs.Sec4.Theorem30.TimeOfBlock

/-!
# Theorem 30 in the light language: limits that are polynomial in N

"Word size", proof of Theorem 30.  For every exponent c of the bound N^c on the entries there are
limits (`lim30`) that the two routines preCore and queryAt can live with (`lim30_ok`) and that are
at most 2^9 ((N + 1) (D + 1))^(20 + 2c) (`small_lim30`).  The exponents are generous: since (10^L)²
≤ N^5, every quantity that depends on L is at most B = (N + 1)^5 (`below`), the block has at most
222 B⁴ cells (`top_sub_le_pow`), and the word bound `word30` is a sum of seven terms, each at most a
small multiple of (N + 1)^(20 + 2c) (`word30_le`).  What the two routines ask of the limits is
`Lim30`, in their specifications.  The polynomial bound is for a block whose base address b0 is at
most 10 (N + 1)³; the end theorems, which put the block behind the input, show this of their b0
(`b0_le`, `wantedB0_le`, `blockAt_le`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec Finset

/-- There are at most `11^L` cubes. -/
theorem card_boxes_le (L m t : ℕ) : (boxes L m t).card ≤ 11 ^ L := by
  have hsymbols : Fintype.card CubeSymbol = 11 := rfl
  calc (boxes L m t).card ≤ (univ : Finset (Cube L)).card := card_filter_le _ _
    _ = 11 ^ L := by rw [card_univ, Fintype.card_fun, hsymbols, Fintype.card_fin]

/-- The number of bands is at most `N + 1`. -/
theorem numBands_le (L m N : ℕ) (hmL : m ≤ L) : numBands L m N ≤ N + 1 := by
  have hband : 1 ≤ bandSize L m :=
    Nat.mul_pos (Nat.sqrt_pos.mpr (Nat.choose_pos hmL)) (Nat.one_le_pow _ _ (by norm_num))
  have hN : N ≤ bandSize L m * N := Nat.le_mul_of_pos_left _ hband
  refine Nat.div_le_of_le_mul ?_
  rw [Nat.mul_add_one]
  omega

/-- `N₀ ≤ N` under the hypotheses of Theorem 30. -/
theorem N0_le_N {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : N0 p.L p.m ≤ p.N := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (K p.L p.m : ℝ) :=
    Real.one_le_sqrt.2 (by exact_mod_cast Nat.choose_pos hmL)
  exact_mod_cast (le_mul_of_one_le_left (Nat.cast_nonneg _) hsqrt).trans h.N_ge

/-- Everything that depends on `L` is at most `B`; see `below` for `B = (N + 1)^5`. -/
structure Below (p : Sec2.Par) (t B : ℕ) : Prop where
  one : 1 ≤ B
  T : 10 ^ p.L ≤ B
  S7 : 7 ^ p.L ≤ B
  L1 : p.L + 1 ≤ B
  tenm : 10 ^ p.m ≤ B
  bx : (boxes p.L p.m t).card ≤ B
  nB : p.nB ≤ B
  N : p.N ≤ B

/-- "Since N ≥ N₀ = 3^{L-m} and L ≥ 10m, we have 10^L ≤ N^{5/2}": so all these quantities are at
most `(10^L)² ≤ N^5`. -/
theorem below {p : Sec2.Par} {t : ℕ} (h : Hyp30 p t) : Below p t ((p.N + 1) ^ 5) := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hsq := Theorem30.ten_pow_le p.L p.m p.N h.L_ge (N0_le_N h)
  have hN5 : p.N ^ 5 ≤ (p.N + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  have hten : 10 ^ p.L ≤ (10 ^ p.L) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hT : 10 ^ p.L ≤ (p.N + 1) ^ 5 := by omega
  have hN1 : p.N + 1 ≤ (p.N + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have hL1 : p.L + 1 ≤ (p.L + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h11 : 11 ^ p.L ≤ (10 ^ p.L) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) _
  exact ⟨by omega, hT, (Nat.pow_le_pow_left (by norm_num) _).trans hT,
    (hL1.trans (succ_sq_le_ten_pow p.L)).trans hT,
    (Nat.pow_le_pow_right (by norm_num) hmL).trans hT,
    (card_boxes_le _ _ _).trans (by omega), (numBands_le p.L p.m p.N hmL).trans hN1, by omega⟩

/-- The length of the block is at most `222 B⁴`. -/
theorem top_sub_le_pow {p : Sec2.Par} {t B : ℕ} (h : Hyp30 p t) (hB : Below p t B) (b0 : ℕ) :
    top p t b0 - b0 ≤ 222 * B ^ 4 := by
  have hmL : p.m ≤ p.L := by have := h.L_ge; omega
  have hL1 : 1 ≤ p.L := by have := h.L_ge; have := h.m_pos; omega
  obtain ⟨hone, hT, -, hL, -, hbx, hnB, hN⟩ := hB
  have hshared := sharedEnd_sub_le p b0 hL1 hmL
  rw [top_sub_eq]
  generalize p.sharedEnd b0 - b0 = E at *
  generalize (boxes p.L p.m t).card = bx at *
  generalize p.nB = nB at *
  generalize 10 ^ p.L = T at *
  -- each product of two of the quantities is at most B², and so on
  have hNL : p.N * (p.L + 1) ≤ B * B := Nat.mul_le_mul hN hL
  have hnT : nB * T ≤ B * B := Nat.mul_le_mul hnB hT
  have hnn : nB * nB ≤ B * B := Nat.mul_le_mul hnB hnB
  have hLb : p.L * bx ≤ B * B := Nat.mul_le_mul (by omega) hbx
  have htries : nB * nB * (11 * (1 + p.L * bx)) ≤ B * B * (11 * (B + B * B)) :=
    Nat.mul_le_mul hnn (by omega)
  -- and every power of B up to the fourth is at most B⁴
  have hpow : ∀ j ≤ 4, B ^ j ≤ B ^ 4 := fun j hj => Nat.pow_le_pow_right hone hj
  have hB0 := hpow 0 (by norm_num)
  have hB1 := hpow 1 (by norm_num)
  have hB2 := hpow 2 (by norm_num)
  have hB3 := hpow 3 (by norm_num)
  rw [pow_zero] at hB0
  rw [pow_one] at hB1
  rw [show B ^ 2 = B * B by ring] at hB2
  rw [show B ^ 3 = B * B * B by ring] at hB3
  rw [show B * B * (11 * (B + B * B)) = 11 * (B * B * B) + 11 * B ^ 4 by ring] at htries
  omega

end Light.Sec4
