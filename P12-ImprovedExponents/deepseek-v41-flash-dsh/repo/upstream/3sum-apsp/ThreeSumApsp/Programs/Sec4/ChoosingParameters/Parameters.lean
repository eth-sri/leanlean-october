/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Setup
public import ThreeSumApsp.Programs.Sec4.Theorem30.Time
public import ThreeSumApsp.TacticsShort

/-!
# Corollaries 26 and 31 in the light language: rational parameters in the program text

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D";
proof of Corollary 31: "with L := ⌈cm⌉ and t := ⌈θm⌉". A program is a finite text, so it can hold c
and θ only if they are rational: c = a/b and θ = p/q (`RatParams`). For real c and θ the statements
follow by approximation (`exists_ratParams`). Corollary 26 is the case c = 21, θ = 1/9, with the
threshold 60 (`ratParams26`).

This file has the parameters, what a structure at the free pointer fr consists of (`structEnd`,
`Ready31`), what the routines ask of the limits (`Lim31`), the query with its specification and its
proof (`QuerySpec31`, `query31_meets`), and the text and the specification of the preprocessing
(`pre31Body`, `PreSpec31`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

/-! ## Parameters -/

/-- The parameters in the program text: c = a/b > 10, θ = p/q in (0, 0.9), and the threshold m₀ ≥ 1
below which queries compute inner products. -/
structure RatParams where
  a : ℕ
  b : ℕ
  p : ℕ
  q : ℕ
  m₀ : ℕ
  hb : 1 ≤ b
  hq : 1 ≤ q
  hc : 10 * b < a
  hp : 1 ≤ p
  hθ : 10 * p < 9 * q
  hm₀ : 1 ≤ m₀

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-- L = ⌈(a/b) m⌉. -/
def RatParams.L (G : RatParams) (m : ℕ) : ℕ := (G.a * m + G.b - 1) / G.b
/-- t = ⌈(p/q) m⌉. -/
def RatParams.t (G : RatParams) (m : ℕ) : ℕ := (G.p * m + G.q - 1) / G.q

/-- 10 m ≤ L. -/
theorem RatParams.ten_le_L (G : RatParams) (m : ℕ) : 10 * m ≤ G.L m := by
  unfold RatParams.L
  rw [Nat.le_div_iff_mul_le G.hb]
  have h1 : 10 * G.b * m ≤ G.a * m := Nat.mul_le_mul_right _ G.hc.le
  have h2 : 10 * m * G.b = 10 * G.b * m := by ring
  have := G.hb
  omega

/-- t ≤ m. -/
theorem RatParams.t_le (G : RatParams) (m : ℕ) : G.t m ≤ m := by
  unfold RatParams.t
  have hq := G.hq
  rw [Nat.div_le_iff_le_mul_add_pred tac_omega]
  have h1 : 10 * G.p * m ≤ 9 * G.q * m := Nat.mul_le_mul_right _ G.hθ.le
  have h2 : G.p * m ≤ G.q * m := by
    have e1 : 10 * G.p * m = 10 * (G.p * m) := by ring
    have e2 : 9 * G.q * m = 9 * (G.q * m) := by ring
    omega
  omega

/-- a m ≤ b L. -/
theorem RatParams.am_le (G : RatParams) (m : ℕ) : G.a * m ≤ G.b * G.L m := by
  unfold RatParams.L
  have hb := G.hb
  have hdiv := Nat.div_add_mod (G.a * m + G.b - 1) G.b
  have hmod := Nat.mod_lt (G.a * m + G.b - 1) (by omega : 0 < G.b)
  omega

/-- p m ≤ q m. -/
theorem RatParams.pm_le (G : RatParams) (m : ℕ) : G.p * m ≤ G.q * m :=
  Nat.mul_le_mul_right _ (by have := G.hθ; omega)

/-- The parameters of Theorem 30. -/
def parOf (G : RatParams) (N D₀ : ℕ) : Sec2.Par := ⟨G.L (logFour D₀), logFour D₀, N⟩
/-- The switching order. -/
def switchOf31 (G : RatParams) (D₀ : ℕ) : ℕ := G.t (logFour D₀)
/-- The hypotheses of Theorem 30 at these parameters. -/
abbrev RatParams.Hyp (G : RatParams) (N D₀ : ℕ) : Prop := Hyp30 (parOf G N D₀) (switchOf31 G D₀)
/-- The cost (8) of the preprocessing of Theorem 30 at these parameters. -/
noncomputable abbrev RatParams.preCost (G : RatParams) (N D₀ : ℕ) : ℝ :=
  cost8 (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N
/-- The cost L ∑ α_d of a query of Theorem 30 at these parameters. -/
noncomputable abbrev RatParams.queryCost (G : RatParams) (D₀ : ℕ) : ℝ :=
  costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀)
/-- The first address after the block of Theorem 30. -/
abbrev RatParams.blockEnd (G : RatParams) (N D₀ fr : ℕ) : ℕ :=
  top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr)
/-- The first address that is not used. -/
def structEnd (G : RatParams) (N D₀ fr : ℕ) : ℕ :=
  if logFour D₀ < G.m₀ then fr + 3 else top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr)

/-- Below the threshold a structure has three cells. -/
theorem structEnd_small (h : logFour D₀ < G.m₀) (N fr : ℕ) : structEnd G N D₀ fr = fr + 3 :=
  if_pos h

/-- For m ≥ m₀ a structure ends with the block of Theorem 30. -/
theorem structEnd_large (h : G.m₀ ≤ logFour D₀) (N fr : ℕ) :
    structEnd G N D₀ fr = G.blockEnd N D₀ fr :=
  if_neg (not_lt.2 h)

/-- The block of Theorem 30 begins after the first three cells. -/
theorem add_three_le_blockAt (N D₀ fr : ℕ) : fr + 3 ≤ blockAt N D₀ fr := by
  unfold blockAt
  omega

/-- The block of Theorem 30 is not empty. -/
theorem RatParams.blockAt_lt_blockEnd (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr < G.blockEnd N D₀ fr :=
  base_lt_top _ _ _

/-- The cells that a query of Theorem 30 writes lie in the block. -/
theorem RatParams.scratch_in_block (G : RatParams) (N D₀ fr : ℕ) :
    blockAt N D₀ fr ≤ aWD (parOf G N D₀) (blockAt N D₀ fr) ∧
      aWD (parOf G N D₀) (blockAt N D₀ fr) + (3 * (parOf G N D₀).L + (parOf G N D₀).m)
        ≤ G.blockEnd N D₀ fr :=
  Sec4.scratch_in_block _ _ _

/-- A structure has at least three cells. -/
theorem add_three_le_structEnd (G : RatParams) (N D₀ fr : ℕ) : fr + 3 ≤ structEnd G N D₀ fr := by
  have hblock := add_three_le_blockAt N D₀ fr
  have hend := G.blockAt_lt_blockEnd N D₀ fr
  by_cases h : logFour D₀ < G.m₀
  · rw [structEnd_small h]
  · rw [structEnd_large (not_lt.1 h)]
    omega

/-- m ≤ L. -/
theorem logFour_le_levels (G : RatParams) (N D₀ : ℕ) : (parOf G N D₀).m ≤ (parOf G N D₀).L := by
  change logFour D₀ ≤ G.L (logFour D₀)
  have := G.ten_le_L (logFour D₀)
  omega

/-- The limits that the two routines need. -/
structure Lim31 (lim : Limits) (G : RatParams) (N D₀ fr : ℕ) (U : ℤ) : Prop where
  std : Std lim
  space : structEnd G N D₀ fr ≤ lim.space
  pow : ((4 ^ logFour D₀ : ℕ) : ℤ) ≤ lim.word
  /-- For the computation of L and t. -/
  mword : ((G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q : ℕ) : ℤ) ≤ lim.word
  m0word : (G.m₀ : ℤ) ≤ lim.word
  ip : (D₀ : ℤ) * (U * U) ≤ lim.word
  large : G.m₀ ≤ logFour D₀ → Lim30 lim (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) U

/-- The numbers formed on the way to L fit in a word. -/
theorem Lim31.wordL (h : Lim31 lim G N D₀ fr U) : ((G.a * logFour D₀ + G.b : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast (by omega :
    G.a * logFour D₀ + G.b ≤ G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q)) h.mword

/-- The numbers formed on the way to t fit in a word. -/
theorem Lim31.wordT (h : Lim31 lim G N D₀ fr U) : ((G.p * logFour D₀ + G.q : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast (by omega :
    G.p * logFour D₀ + G.q ≤ G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q)) h.mword

/-- **What both routines are given**: matrices X and Y with entries bounded by U, the addresses aX
and aY of their cells, which lie below the free pointer fr, and limits that suffice. -/
structure Input31 (lim : Limits) (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (U : ℤ) : Prop where
  one_le_D : 1 ≤ D₀
  one_le_N : 1 ≤ N
  lim : Lim31 lim G N D₀ fr U
  absX : ∀ i j, |X i j| ≤ U
  absY : ∀ i j, |Y i j| ≤ U
  belowX : aX + N * D₀ ≤ fr
  belowY : aY + D₀ * N ≤ fr

theorem Input31.zero_le_U (h : Input31 lim G X Y aX aY fr U) : 0 ≤ U :=
  le_trans (abs_nonneg _) (h.absX ⟨0, h.one_le_N⟩ ⟨0, h.one_le_D⟩)

/-! ## The query: the text is query31Body -/

/-- The time of a query. -/
def tQuery31 (G : RatParams) (D₀ : ℕ) : ℕ :=
  (if logFour D₀ < G.m₀ then tIpAt D₀ else tQueryAt (G.L (logFour D₀)) (logFour D₀)
      (switchOf31 G D₀)) + 20

/-! ## The preprocessing: text and interface -/

/-- The time of ceilMul: it counts up to ⌈a m / b⌉. -/
def tCeilMul (a m : ℕ) : ℕ := 20 * (a * m) + 40

/-- Procedure number pn returns ⌈a m / b⌉ on the argument m, and changes no cell. -/
def CeilMulSpec (lim : Limits) (P : Program) (pn a b : ℕ) : Prop :=
  ∀ (m : ℕ) (μ : ℕ → ℤ), ((a * m + b : ℕ) : ℤ) ≤ lim.word → ∀ d, d ≤ lim.depth →
    Meets lim P pn d [m] μ (tCeilMul a m) fun r μ' => r = ((a * m + b - 1) / b : ℕ) ∧ μ' = μ

namespace Pre31

/-- The locals of pre31. The first five are its arguments N, D, aX, aY, fr. Then come m, 4^m, L, t,
the addresses of the padded matrices, the base address b0 of the block of Theorem 30, a result that
is not used, and the product N 4^m. -/
abbrev Size : ℕ := 0
 abbrev Dim : ℕ := 1
 abbrev MatX : ℕ := 2
 abbrev MatY : ℕ := 3
 abbrev Free : ℕ := 4
 abbrev Log : ℕ := 5
 abbrev Padded : ℕ := 6
 abbrev Levels : ℕ := 7
 abbrev Switch : ℕ := 8
 abbrev PadX : ℕ := 9
 abbrev PadY : ℕ := 10
 abbrev Block : ℕ := 11
 abbrev Res : ℕ := 12
 abbrev Area : ℕ := 13

end Pre31

open Pre31
/-- The first part of pre31 for m ≥ m₀: L, t, the addresses, and the padded matrices. -/
def prePad31 : Stmt :=
  .set Padded (M (v Free +' k 2)) ;;
  .call Proc.levels31 [v Log] Levels ;;
  .call Proc.switch31 [v Log] Switch ;;
  .set PadX (v Free +' k 3) ;;
  .set Area (v Size *' v Padded) ;;
  .set PadY (v PadX +' v Area) ;;
  .set Block (v PadY +' v Area) ;;
  .call Proc.padX [v Size, v Dim, v Padded, v MatX, v PadX] Res ;;
  .call Proc.copy [v MatY, v PadY, v Dim *' v Size] Res ;;
  .call Proc.fill [v PadY +' v Dim *' v Size, (v Padded -' v Dim) *' v Size, k 0] Res

open Pre31
/-- The second part: the preprocessing of Theorem 30, the base address and the flag 1. -/
def preBuild31 : Stmt :=
  .call Proc.preCore [v Levels, v Log, v Switch, v Size, v Padded, v PadX, v PadY, v Block] Res ;;
  .store (v Free +' k 1) (v Block) ;;
  .store (v Free) (k 1)

/-- The part of pre31 for m ≥ m₀. -/
def preLarge31 : Stmt := prePad31 ;; preBuild31

open Pre31
/-- pre31(N, D, aX, aY, fr): m and 4^m; for m < m₀ the flag 0, for m ≥ m₀ preLarge31. -/
def pre31Body (G : RatParams) : Stmt :=
  .call Proc.log4 [v Dim, v Free +' k 2] Log ;;
  .ite (v Log <' k G.m₀) (.store (v Free) (k 0)) preLarge31

/-- The time of the preprocessing; c is the constant of the shared stage. -/
def tPre31 (c : ℕ) (G : RatParams) (N D₀ : ℕ) : ℕ :=
  tLog4 (logFour D₀) + 30 +
    if logFour D₀ < G.m₀ then 0 else
      tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀))
        + tCopy (D₀ * N) + tFill ((D (logFour D₀) - D₀) * N)
        + tPreCore c (parOf G N D₀) (switchOf31 G D₀) + 120

end Light.Sec4