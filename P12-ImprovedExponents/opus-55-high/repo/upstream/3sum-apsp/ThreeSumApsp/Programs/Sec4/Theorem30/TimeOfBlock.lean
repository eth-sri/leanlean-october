/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec4.Theorem30.Time

/-!
# Theorem 30 in the light language: the two routines against the expressions (8) and L ∑ α_d

Pure arithmetic, continued. Every summand of the time of the shared stage and of the length of the
shared block is at most a constant times `10^L`, or `N (L + 1)`, or the work for the bands
(`sharedShape_le`, `sharedEnd_sub_le`), and these three are within (8). With the tiles of the
previous file this gives the three bounds that leave these two files: the preprocessing takes
`O((8))` steps (`exists_tPreCore_le`), the block has `O((8))` cells (`exists_top_sub_le`), and a
query takes `O(L ∑_{d ≤ t} α_d)` steps (`exists_tQueryAt_le`).  The offline form uses them
elsewhere: its expression (9) is (8) plus |W| times the cost of a query (`Theorem30.cost9_eq`, with
the mathematics of Theorem 30), and `exists_tWantedCore_le`, beside the offline statement, puts the
two bounds together.
-/


namespace Light.Sec4

open ThreeSumApsp

/-! ## The shared stage, in natural numbers -/

/-- `(L + 1)² ≤ 10^L`. -/
theorem succ_sq_le_ten_pow (L : ℕ) : (L + 1) ^ 2 ≤ 10 ^ L := by
  have hfour : (L + 1) ^ 2 ≤ 4 ^ L := by
    induction L with
    | zero => simp
    | succ L ih =>
      grind
  exact hfour.trans (by simp_all [Nat.pow_le_pow_left])

/-- The facts about the sizes that the two estimates below use; T is `10^L` and S7 is `7^L`. -/
structure SizeFacts (L m K KK N0 D S7 T : ℕ) : Prop where
  sq : (L + 1) ^ 2 ≤ T
  KL : K * L ≤ T
  KND : K * N0 * D ≤ S7
  LS : L * S7 ≤ 2 * T
  ST : S7 ≤ T
  KK_le : KK ≤ K
  K_pos : 1 ≤ K
  N0_pos : 1 ≤ N0
  D_pos : 1 ≤ D
  L_pos : 1 ≤ L
  mL : m ≤ L

variable (p : Sec2.Par)

theorem sizeFacts (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    SizeFacts p.L p.m p.K p.KK p.N0 p.D p.S7 p.T :=
  ⟨succ_sq_le_ten_pow p.L, Theorem30.subsets p.L p.m, Theorem30.K_mul_N0_mul_D_le p.L p.m,
    Theorem30.form_array p.L, Nat.pow_le_pow_left (by norm_num) p.L, Nat.sqrt_le _,
    Nat.choose_pos hmL, Nat.one_le_pow _ _ (by norm_num), Nat.one_le_pow _ _ (by norm_num), hL1,
    hmL⟩

/-- The length of the shared block. -/
theorem sharedEnd_sub_le (b0 : ℕ) (hL1 : 1 ≤ p.L) (hmL : p.m ≤ p.L) :
    p.sharedEnd b0 - b0 ≤ 190 * 10 ^ p.L + 2 * (p.N * (p.L + 1)) + 2 * (p.nB * 10 ^ p.L) := by
  obtain ⟨sq, KL, KND, LS, ST, KKle, K1, N1, D1, L1, mL⟩ := sizeFacts p hL1 hmL
  have hLo : p.Lo ≤ p.L := Nat.sub_le _ _
  simp only [Sec2.Par.sharedEnd, Sec2.Par.aZS, Sec2.Par.aARR, Sec2.Par.aENCB, Sec2.Par.aENCA,
    Sec2.Par.aDIG4, Sec2.Par.aDIG3, Sec2.Par.aBLOCK, Sec2.Par.aBAND, Sec2.Par.aMASK, Sec2.Par.aPSI,
    Sec2.Par.aPHI, Sec2.Par.aPAS, Sec2.Par.aP10, Sec2.Par.aP7, Sec2.Par.aP4, Sec2.Par.aP3]
  change _ ≤ 190 * p.T + 2 * (p.N * (p.L + 1)) + 2 * (p.nB * p.T)
  generalize p.S7 = S7 at *
  generalize p.K = K at *
  generalize p.KK = KK at *
  generalize p.D = D at *
  generalize p.Lo = Lo at *
  generalize p.N = N at *
  generalize p.L = L at *
  generalize p.m = m at *
  have hmask : KK * L ≤ K * L := Nat.mul_le_mul_right _ KKle
  have hdig3 : N * Lo ≤ N * L := Nat.mul_le_mul_left _ hLo
  have hdig4 : D * m ≤ L * S7 := (Nat.mul_le_mul (le_trans (Nat.le_mul_of_pos_left _ (by positivity)) KND) mL).trans (by grind)
  grind

/-! ## Within (8) -/

/-- The length of the block, split into the shared block, the scratch strings, and the tries with
their roots. -/
theorem top_sub_eq (t b0 : ℕ) :
    top p t b0 - b0 = (p.sharedEnd b0 - b0) + (3 * p.L + p.m + 2)
      + (1 + p.nB * p.nB * (11 * (1 + p.L * (boxes p.L p.m t).card)) + p.nB * p.nB) := by
  grind [base_le_sharedEnd, top, aTR, aROOTS, aFP, aSS, aBOX, aCUR, aWD, trieCap]

/-- **A query** takes `O(L ∑_{d ≤ t} α_d)` steps. -/
theorem exists_tQueryAt_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Sec2.Par) (t : ℕ), Hyp30 p t →
    (tQueryAt p.L p.m t : ℝ) ≤ C * costQuery p.L p.m t := by
  obtain ⟨C, hC, hcore⟩ := exists_tQueryCore_le
  refine ⟨C + 510, by positivity, fun p t h => ?_⟩
  have hcore := hcore p.L p.m t h.L_pos h.m_le h.t_le
  have hL := cast_L_le_costQuery p.L p.m t
  have hL1 : (1 : ℝ) ≤ p.L := by exact_mod_cast h.L_pos
  -- tQueryAt = 70 L + 440 + tQueryCore
  unfold tQueryAt tOutDigits
  grind
