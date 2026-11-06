/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Setup
public import ThreeSumApsp.Programs.Sec4.Theorem30.Time

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
  (a b p q m₀ : ℕ)
  hb : 1 ≤ b
  hq : 1 ≤ q
  hc : 10 * b < a
  hθ : 10 * p < 9 * q

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : ThreeSumApsp.IntMatrix N D₀}
  {Y : ThreeSumApsp.IntMatrix D₀ N} {aX aY fr : ℕ} {U : ℤ} {μ μ' : Light.Memory}

/-- L = ⌈(a/b) m⌉. -/
def RatParams.L (G : RatParams) m := (G.a * m + G.b - 1) / G.b
/-- t = ⌈(p/q) m⌉. -/
def RatParams.t (G : RatParams) m := (G.p * m + G.q - 1) / G.q

/-- 10 m ≤ L. -/
theorem RatParams.ten_le_L (G : RatParams) m : 10 * m ≤ G.L m := by
  unfold RatParams.L
  rw [Nat.le_div_iff_mul_le G.hb]
  have  : 10 * G.b * m ≤ G.a * m := Nat.mul_le_mul_right _ G.hc.le
  have  : 10 * m * G.b = 10 * G.b * m := by ring
  have := G.hb
  omega

/-- t ≤ m. -/
theorem RatParams.t_le (G : RatParams) m : G.t m ≤ m := by
  unfold RatParams.t
  have hq := G.hq
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have  : 10 * G.p * m ≤ 9 * G.q * m := Nat.mul_le_mul_right _ G.hθ.le
  grind

/-- a m ≤ b L. -/
theorem RatParams.am_le (G : RatParams) m : G.a * m ≤ G.b * G.L m := by
  unfold RatParams.L
  have hb := G.hb
  have  := Nat.div_add_mod (G.a * m + G.b - 1) G.b
  have  := Nat.mod_lt (G.a * m + G.b - 1) (by omega : 0 < G.b)
  omega

/-- p m ≤ q m. -/
theorem RatParams.pm_le (G : RatParams) m : G.p * m ≤ G.q * m :=
  Nat.mul_le_mul_right _ (by have := G.hθ; omega)

/-- The parameters of Theorem 30. -/
def parOf (G : RatParams) (N D₀ : ℕ) : Sec2.Par := ⟨G.L (logFour D₀), logFour D₀, N⟩
/-- The switching order. -/
def switchOf31 (G : RatParams) D₀ := G.t (logFour D₀)
/-- The hypotheses of Theorem 30 at these parameters. -/
abbrev RatParams.Hyp G N D₀ := Hyp30 (parOf G N D₀) (switchOf31 G D₀)
/-- The cost (8) of the preprocessing of Theorem 30 at these parameters. -/
noncomputable abbrev RatParams.preCost G N D₀ :=
  cost8 (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N
/-- The cost L ∑ α_d of a query of Theorem 30 at these parameters. -/
noncomputable abbrev RatParams.queryCost G D₀ :=
  costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀)
/-- The first address after the block of Theorem 30. -/
abbrev RatParams.blockEnd G N D₀ fr :=
  top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr)
/-- The first address that is not used. -/
def structEnd G N D₀ fr :=
  if logFour D₀ < G.m₀ then fr + 3 else top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr)

/-- Below the threshold a structure has three cells. -/
theorem structEnd_small (h : logFour D₀ < G.m₀) N fr : structEnd G N D₀ fr = fr + 3 :=
  if_pos h

/-- For m ≥ m₀ a structure ends with the block of Theorem 30. -/
theorem structEnd_large (h : G.m₀ ≤ logFour D₀) N fr :
    structEnd G N D₀ fr = G.blockEnd N D₀ fr :=
  if_neg (not_lt.2 h)

/-- The block of Theorem 30 begins after the first three cells. -/
theorem add_three_le_blockAt N D₀ fr : fr + 3 ≤ blockAt N D₀ fr := by
  unfold blockAt
  omega

/-- The block of Theorem 30 is not empty. -/
theorem RatParams.blockAt_lt_blockEnd (G : RatParams) N D₀ fr :
    blockAt N D₀ fr < G.blockEnd N D₀ fr :=
  base_lt_top _ _ _

/-- The cells that a query of Theorem 30 writes lie in the block. -/
theorem RatParams.scratch_in_block G N D₀ fr :
    blockAt N D₀ fr ≤ aWD (parOf G N D₀) (blockAt N D₀ fr) ∧
      aWD (parOf G N D₀) (blockAt N D₀ fr) + (3 * (parOf G N D₀).L + (parOf G N D₀).m)
        ≤ G.blockEnd N D₀ fr :=
  Sec4.scratch_in_block _ _ _

/-- A structure has at least three cells. -/
theorem add_three_le_structEnd G N D₀ fr : fr + 3 ≤ structEnd G N D₀ fr := by
  have  := add_three_le_blockAt N D₀ fr
  have  := G.blockAt_lt_blockEnd N D₀ fr
  grind [structEnd_small, structEnd_large]

/-- m ≤ L. -/
theorem logFour_le_levels G N D₀ : (parOf G N D₀).m ≤ (parOf G N D₀).L := by
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

variable (h : Lim31 lim G N D₀ fr U)

include h in
/-- The numbers formed on the way to L fit in a word. -/
theorem Lim31.wordL  : ((G.a * logFour D₀ + G.b : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by omega) h.mword

include h in
/-- The numbers formed on the way to t fit in a word. -/
theorem Lim31.wordT  : ((G.p * logFour D₀ + G.q : ℕ) : ℤ) ≤ lim.word :=
  le_trans (by omega) h.mword

/-- **What both routines are given**: matrices X and Y with entries bounded by U, the addresses aX
and aY of their cells, which lie below the free pointer fr, and limits that suffice. -/
structure Input31 (lim : Limits) (G : RatParams) {N D₀ : ℕ} (X : ThreeSumApsp.IntMatrix N D₀)
    (Y : ThreeSumApsp.IntMatrix D₀ N) (aX aY fr : ℕ) (U : ℤ) : Prop where
  one_le_D : 1 ≤ D₀
  one_le_N : 1 ≤ N
  lim : Lim31 lim G N D₀ fr U
  absX : ∀ i j, |X i j| ≤ U
  absY : ∀ i j, |Y i j| ≤ U
  belowX : aX + N * D₀ ≤ fr
  belowY : aY + D₀ * N ≤ fr

def Input31.zero_le_U (h : Input31 lim G X Y aX aY fr U) :=
  le_trans (abs_nonneg _) (h.absX ⟨0, h.one_le_N⟩ ⟨0, h.one_le_D⟩)

/-! ## The query: the text is query31Body -/

/-- The time of a query. -/
def tQuery31 G D₀ :=
  (if logFour D₀ < G.m₀ then tIpAt D₀ else tQueryAt (G.L (logFour D₀)) (logFour D₀)
      (switchOf31 G D₀)) + 20

/-! ## The preprocessing: text and interface -/

/-- The time of ceilMul: it counts up to ⌈a m / b⌉. -/
def tCeilMul a m := 20 * (a * m) + 40

/-- Procedure number pn returns ⌈a m / b⌉ on the argument m, and changes no cell. -/
def CeilMulSpec (lim : Limits) (P : Program) (pn a b : ℕ) : Prop :=
  ∀ (m : ℕ) (μ : Light.Memory), ((a * m + b : ℕ) : ℤ) ≤ lim.word → ∀ d, d ≤ lim.depth →
    Meets lim P pn d [m] μ (tCeilMul a m) fun r μ' => r = ((a * m + b - 1) / b : ℕ) ∧ μ' = μ


/-- The first part of pre31 for m ≥ m₀: L, t, the addresses, and the padded matrices. -/
def prePad31  :=
  .set 6 (M (v 4 +' k 2)) ;;
  .call 72 [v 5] 7 ;;
  .call 73 [v 5] 8 ;;
  .set 9 (v 4 +' k 3) ;;
  .set 13 (v 0 *' v 6) ;;
  .set 10 (v 9 +' v 13) ;;
  .set 11 (v 10 +' v 13) ;;
  .call 62 [v 0, v 1, v 6, v 2, v 9] 12 ;;
  .call 58 [v 3, v 10, v 1 *' v 0] 12 ;;
  .call 59 [v 10 +' v 1 *' v 0, (v 6 -' v 1) *' v 0, k 0] 12

/-- The time of the preprocessing; c is the constant of the shared stage. -/
def tPre31 c G N D₀ :=
  tLog4 (logFour D₀) + 30 +
    if logFour D₀ < G.m₀ then 0 else
      tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀))
        + tCopy (D₀ * N) + tFill ((D (logFour D₀) - D₀) * N)
        + tPreCore c (parOf G N D₀) (switchOf31 G D₀) + 120

end Light.Sec4
