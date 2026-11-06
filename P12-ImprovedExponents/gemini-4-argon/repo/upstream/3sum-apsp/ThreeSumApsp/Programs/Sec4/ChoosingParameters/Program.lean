module

public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts
public import ThreeSumApsp.Programs.Sec4.Theorem30.Memory
public import ThreeSumApsp.Sec4.Corollary31
public import ThreeSumApsp.Util.Ceil
public import ThreeSumApsp.Programs.Sec4.Theorem30.Time
public import ThreeSumApsp.Programs.Sec4.Theorem30.Areas
public import ThreeSumApsp.Lang.RowMajor
public import ThreeSumApsp.Programs.Sec4.Theorem30.WordSize
public import ThreeSumApsp.Programs.Sec4.Theorem30.Program
public import ThreeSumApsp.Sec4.Table2.LogBounds
public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Log
public import ThreeSumApsp.Sec4.Corollary31.RationalParameters

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

namespace Proc
abbrev copy : ℕ := 58
abbrev fill : ℕ := 59
abbrev log4 : ℕ := 60
abbrev padX : ℕ := 62
abbrev ipAt : ℕ := 63
abbrev query31 : ℕ := 65
abbrev levels31 : ℕ := 72
abbrev switch31 : ℕ := 73
end Proc

/-! ## Time functions -/

def tCopy (n : ℕ) : ℕ := 16 * n + 6
def tFill (n : ℕ) : ℕ := 13 * n + 6
def tLog4 (m : ℕ) : ℕ := 20 * m + 20
/-- For each row: a copy, a fill, and the arithmetic of the addresses. -/
def tPadX (N D' : ℕ) : ℕ := N * (16 * D' + 80) + 10
def tIpAt (D : ℕ) : ℕ := 40 * D + 20

/-! ## The small routines -/

/-- copy(src, dst, n). -/
def CopySpec (lim : Limits) (P : Program) : Prop :=
  ∀ (src dst n : ℕ) (μ : ℕ → ℤ), src + n ≤ lim.space → dst + n ≤ lim.space → n < lim.space →
      (src + n ≤ dst ∨ dst + n ≤ src) →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.copy d [src, dst, n] μ (tCopy n) fun _ μ' =>
        (∀ i < n, μ' (dst + i) = μ (src + i)) ∧ SameOutside μ μ' dst n

/-- fill(dst, n, x). -/
def FillSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (dst n : ℕ) (x : ℤ) (μ : ℕ → ℤ), dst + n ≤ lim.space → n < lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.fill d [dst, n, x] μ (tFill n) fun _ μ' =>
        (∀ i < n, μ' (dst + i) = x) ∧ SameOutside μ μ' dst n

/-- log4(D, a) returns m = ⌈log₄ D⌉ and writes 4^m to the cell a. -/
def Log4Spec (lim : Limits) (P : Program) : Prop :=
  ∀ (D₀ a : ℕ) (μ : ℕ → ℤ), a < lim.space → ((4 ^ Nat.clog 4 D₀ : ℕ) : ℤ) ≤ lim.word →
      (Nat.clog 4 D₀ : ℤ) ≤ lim.word →
    ∀ d, d ≤ lim.depth → Meets lim P Proc.log4 d [D₀, a] μ (tLog4 (Nat.clog 4 D₀)) fun r μ' =>
      r = Nat.clog 4 D₀ ∧ μ' = Function.update μ a ((4 ^ Nat.clog 4 D₀ : ℕ) : ℤ)

/-- padX(N, D, D', aX, aX') writes X, padded with zero columns to D' columns, to aX'. -/
def PadXSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (N D₀ D' aX aX' : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (μ : ℕ → ℤ), D₀ ≤ D' → 1 ≤ D' →
      MatAt μ aX X → aX + N * D₀ ≤ aX' →
    aX' + N * D' < lim.space →
    ∀ d, d + 1 ≤ lim.depth → Meets lim P Proc.padX d [N, D₀, D', aX, aX'] μ (tPadX N D') fun _ μ' =>
      MatAt μ' aX' (padInnerCols D' X) ∧ SameOutside μ μ' aX' (N * D')

/-- ipAt(I, J, N, D, aX, aY) returns (XY)[I, J] as an inner product. -/
def IpAtSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (N D₀ aX aY : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ) (I J : Fin N),
    1 ≤ D₀ → MatAt μ aX X → MatAt μ aY Y → (∀ i j, |X i j| ≤ U) →
        (∀ i j, |Y i j| ≤ U) → aX + N * D₀ < lim.space →
    aY + D₀ * N < lim.space → (D₀ : ℤ) * (U * U) ≤ lim.word →
    ∀ d, d ≤ lim.depth →
    Meets lim P Proc.ipAt d [(I : ℕ), (J : ℕ), N, D₀, aX, aY] μ (tIpAt D₀) fun r μ' =>
        r = (X * Y) I J ∧ μ' = μ

/-! ### copy and fill are those of the library -/

theorem copy_ok {lim : Limits} {P : Program} (hP : P[Proc.copy]? = some copyBody)
    (hstd : Std lim) : CopySpec lim P := by
  intro src dst n μ h1 h2 _ h4 d _
  exact copy_meets hP hstd.space_le h1 h2 h4

theorem fill_ok {lim : Limits} {P : Program} (hP : P[Proc.fill]? = some fillBody)
    (hstd : Std lim) : FillSpec lim P := by
  intro dst n x μ h1 _ d _
  refine (fill_meets hP hstd.space_le h1).mono le_rfl fun _ μ' h => ⟨fun i hi => ?_, h.2⟩
  have := h.1 i (by simpa using hi)
  simpa using this

/-! ### ⌈log₄ D⌉ -/

namespace Log4

/-- The locals of log4: the argument D, which the result replaces; the address a; the power of 4;
and its exponent. -/
abbrev Dim : ℕ := 0
@[inherit_doc Dim] abbrev Cell : ℕ := 1
@[inherit_doc Dim] abbrev Power : ℕ := 2
@[inherit_doc Dim] abbrev Exp : ℕ := 3

end Log4

open Log4 in
/-- log4(D, a): multiply by 4 until D is reached; store the power at a and return the exponent. -/
def log4Body : Stmt :=
  .set Power (k 1) ;; .set Exp (k 0) ;;
  .while (v Power <' v Dim) (.set Power (v Power *' k 4) ;; .set Exp (v Exp +' k 1)) ;;
  .store (v Cell) (v Power) ;; .set Dim (v Exp)

theorem log4_meets {lim : Limits} {P : Program} (hP : P[Proc.log4]? = some log4Body)
    (hstd : Std lim) : Log4Spec lim P := by
  intro D₀ a μ ha hw hmw
  refine fun d _ => ⟨log4Body, hP, ?_⟩
  have := hstd.const_le
  obtain ⟨F, hF⟩ : ∃ F, F = 4 ^ Nat.clog 4 D₀ := ⟨_, rfl⟩
  have : D₀ ≤ F := hF ▸ Nat.le_pow_clog (by norm_num) D₀
  rw [← hF] at hw ⊢
  unfold log4Body tLog4
  -- pow := 1 ; exp := 0
  light_set 1
  light_set 0
  -- while pow < D: pow := pow * 4 ; exp := exp + 1.  Before round i, pow = 4^i and exp = i.
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [D₀, a, ((4 ^ i : ℕ) : ℤ), i], μ⟩)
    (Nat.clog 4 D₀) rfl ?round ?done (hT := le_rfl))
  case round =>
    rintro i _ hi rfl
    have hlt := (Nat.lt_clog_iff_pow_lt (by norm_num)).1 hi
    have hpow : 4 ^ i * 4 ≤ F := by
      rw [hF, ← pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) hi
    rw [pow_succ]
    generalize 4 ^ i = p at hlt hpow ⊢
    exact ⟨by light_side, by simp; omega, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    rw [← hF]
    refine ⟨by light_side, by simp; omega, ?_⟩
    -- mem[a] := pow ; return exp
    light_store a F
    light_set (Nat.clog 4 D₀ : ℤ)
    exact ⟨rfl, rfl⟩


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Corollaries 26 and 31 in the light language: m, the places of the padded matrices, the query

m = ⌈log₄ D⌉ (`logFour`), the places of the padded matrices and of the block of Theorem 30 behind
the free pointer (`paddedXAt`, `paddedYAt`, `blockAt`), the text of the query, and the bounds on the
entries of the padded matrices. The text of the query serves all rational parameters; its
specification is `QuerySpec31`, proved in `query31_meets`.
-/




/-! ## Parameters and map -/

/-- m = ⌈log₄ D⌉. -/
def logFour (D₀ : ℕ) : ℕ := Nat.clog 4 D₀
/-- The address of the padded X. -/
def paddedXAt (fr : ℕ) : ℕ := fr + 3
/-- The address of the padded Y. -/
def paddedYAt (N D₀ fr : ℕ) : ℕ := fr + 3 + N * D (logFour D₀)
/-- The base address of the block of Theorem 30. -/
def blockAt (N D₀ fr : ℕ) : ℕ := fr + 3 + N * D (logFour D₀) + N * D (logFour D₀)
/-! ## The query -/

namespace Query31

/-- The locals of query31 are its arguments I, J, N, D, aX, aY, fr; the answer replaces I. -/
abbrev Row : ℕ := 0
@[inherit_doc Row] abbrev Col : ℕ := 1
@[inherit_doc Row] abbrev Size : ℕ := 2
@[inherit_doc Row] abbrev Dim : ℕ := 3
@[inherit_doc Row] abbrev MatX : ℕ := 4
@[inherit_doc Row] abbrev MatY : ℕ := 5
@[inherit_doc Row] abbrev Free : ℕ := 6

end Query31

open Query31 in
/-- query31(I, J, N, D, aX, aY, fr): if the flag is 1, the query of Theorem 30, and otherwise the
inner product. -/
def query31Body : Stmt :=
  .ite (M (v Free) =' k 1) (.call Proc.queryAt [v Row, v Col, M (v Free +' k 1)] Row)
    (.call Proc.ipAt [v Row, v Col, v Size, v Dim, v MatX, v MatY] Row)

theorem abs_padInnerCols_le {N D₀ D' : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {U : ℤ}
    (h : ∀ i j, |X i j| ≤ U) (hU : 0 ≤ U) (i : Fin N) (j : Fin D') :
    |padInnerCols D' X i j| ≤ U := by
  unfold padInnerCols
  split_ifs
  · exact h _ _
  · simpa using hU

theorem abs_padInnerRows_le {N D₀ D' : ℕ} {Y : Matrix (Fin D₀) (Fin N) ℤ} {U : ℤ}
    (h : ∀ i j, |Y i j| ≤ U) (hU : 0 ≤ U) (i : Fin D') (j : Fin N) :
    |padInnerRows D' Y i j| ≤ U := by
  unfold padInnerRows
  split_ifs
  · exact h _ _
  · simpa using hU

theorem le_D_logFour (D₀ : ℕ) : D₀ ≤ D (logFour D₀) := Nat.le_pow_clog (by norm_num) D₀

/-- The ceiling ⌈log₄ D⌉ in natural numbers. -/
theorem ceil_logb_four (D₀ : ℕ) : ⌈Real.logb 4 (D₀ : ℝ)⌉₊ = logFour D₀ := by
  have := Real.natCeil_logb_natCast 4 D₀
  simpa [logFour] using this

/-- m ≤ 4 D, because m ≤ 4^m ≤ 4 D. -/
theorem logFour_le_four_mul {D₀ : ℕ} (hD : 1 ≤ D₀) : logFour D₀ ≤ 4 * D₀ :=
  le_trans (Nat.lt_pow_self (by norm_num)).le (Nat.pow_clog_le_mul (b := 4) (by norm_num) hD)

/-- m ≥ 1 means D ≥ 2. -/
theorem two_le_of_clog {D₀ : ℕ} (h : 1 ≤ logFour D₀) : 2 ≤ D₀ := by
  by_contra hc
  have : logFour D₀ = 0 := Nat.clog_of_right_le_one (by omega) 4
  omega



/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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
  hθ : 10 * p < 9 * q

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
  have : 10 * G.b * m ≤ G.a * m := Nat.mul_le_mul_right _ G.hc.le
  have : 10 * m * G.b = 10 * G.b * m := by ring
  have := G.hb
  omega

/-- t ≤ m. -/
theorem RatParams.t_le (G : RatParams) (m : ℕ) : G.t m ≤ m := by
  unfold RatParams.t
  have hq := G.hq
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have : 10 * G.p * m ≤ 9 * G.q * m := Nat.mul_le_mul_right _ G.hθ.le
  have : G.p * m ≤ G.q * m := by
    have : 10 * G.p * m = 10 * (G.p * m) := by ring
    have : 9 * G.q * m = 9 * (G.q * m) := by ring
    omega
  omega

/-- a m ≤ b L. -/
theorem RatParams.am_le (G : RatParams) (m : ℕ) : G.a * m ≤ G.b * G.L m := by
  unfold RatParams.L
  have hb := G.hb
  have := Nat.div_add_mod (G.a * m + G.b - 1) G.b
  have := Nat.mod_lt (G.a * m + G.b - 1) (by omega : 0 < G.b)
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
  have := add_three_le_blockAt N D₀ fr
  have := G.blockAt_lt_blockEnd N D₀ fr
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
@[inherit_doc Size] abbrev Dim : ℕ := 1
@[inherit_doc Size] abbrev MatX : ℕ := 2
@[inherit_doc Size] abbrev MatY : ℕ := 3
@[inherit_doc Size] abbrev Free : ℕ := 4
@[inherit_doc Size] abbrev Log : ℕ := 5
@[inherit_doc Size] abbrev Padded : ℕ := 6
@[inherit_doc Size] abbrev Levels : ℕ := 7
@[inherit_doc Size] abbrev Switch : ℕ := 8
@[inherit_doc Size] abbrev PadX : ℕ := 9
@[inherit_doc Size] abbrev PadY : ℕ := 10
@[inherit_doc Size] abbrev Block : ℕ := 11
@[inherit_doc Size] abbrev Res : ℕ := 12
@[inherit_doc Size] abbrev Area : ℕ := 13

end Pre31

open Pre31 in
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

/-- The time of the preprocessing; c is the constant of the shared stage. -/
def tPre31 (c : ℕ) (G : RatParams) (N D₀ : ℕ) : ℕ :=
  tLog4 (logFour D₀) + 30 +
    if logFour D₀ < G.m₀ then 0 else
      tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀))
        + tCopy (D₀ * N) + tFill ((D (logFour D₀) - D₀) * N)
        + tPreCore c (parOf G N D₀) (switchOf31 G D₀) + 120


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Theorem 30, the offline form (9): preprocess, then one query for each wanted position

Theorem 30: "In particular, for every set W of positions of an N × N matrix, the entries (XY)[I, J],
(I, J) ∈ W, can be computed deterministically in time
O(L |W| ∑_{d=0}^{t} α_d + L m ρ^t/(1 - ρ) N² + N · 10^L/(√K N₀))."

wantedCore is relocatable: it receives the addresses of the matrices, of the two lists of indices,
of the output and of the free block. It meets its specification `WantedCoreSpec` in every program
that meets those of preCore and queryAt (`wantedCore_spec`): one call of preCore, then a loop whose
round asks one query and stores the answer (`wantedAsk_ends`), with the invariant `Answered`.
-/




/-! ## One query for each wanted position: the invariant -/

variable {Ready : (ℕ → ℤ) → Prop} {Kept Quiet : ℕ → Prop} {out i : ℕ} {ans : List ℤ}
  {μ μ' μ'' : ℕ → ℤ}

/-- The invariant of a loop that asks one query after the other and stores the answers ans from the
address out on, before query i.  The memory is Ready for a query, the first i answers are in place,
and the cells in Kept outside these i cells are as in the memory μ at the start. -/
structure Answered (Ready : (ℕ → ℤ) → Prop) (Kept : ℕ → Prop) (out : ℕ) (ans : List ℤ) (μ : ℕ → ℤ)
    (i : ℕ) (μ' : ℕ → ℤ) : Prop where
  ready : Ready μ'
  answers : Seg μ' out (ans.take i)
  same : SameOn (fun a => Outside out i a ∧ Kept a) μ μ'

/-- One round: a query that leaves the cells in Quiet alone, among them the output and the cells in
Kept, and the store of its answer behind the answers that are there. -/
theorem Answered.step (h : Answered Ready Kept out ans μ i μ') (hi : i < ans.length)
    (hquery : SameOn Quiet μ' μ'') (hout : ∀ j < i, Quiet (out + j)) (hkept : ∀ a, Kept a → Quiet a)
    (hready : Ready (Function.update μ'' (out + i) ans[i])) :
    Answered Ready Kept out ans μ (i + 1) (Function.update μ'' (out + i) ans[i]) := by
  have hlen : (ans.take i).length = i := by rw [List.length_take, Nat.min_eq_left hi.le]
  refine ⟨hready, ?_, ?_⟩
  · have hsnoc := (h.answers.of_sameOn hquery fun j hj => hout j (hlen ▸ hj)).snoc ans[i]
    rw [hlen] at hsnoc
    rwa [List.take_add_one, List.getElem?_eq_getElem hi]
  · exact ((h.same.mono fun a ha => ⟨by have := ha.1; omega, ha.2⟩).then hquery
      fun a ha => ⟨ha, hkept a ha.2⟩).write (by omega) _

/-- A cell of a list that stood in the memory at the start, away from the answers and in Kept, still
holds its entry. -/
theorem Answered.read (h : Answered Ready Kept out ans μ i μ') {a j : ℕ} {l : List ℤ}
    (hl : Seg μ a l) (hj : j < l.length) (hoff : Outside out i (a + j)) (hkept : Kept (a + j)) :
    μ' (a + j) = l[j] :=
  (h.same _ ⟨hoff, hkept⟩).trans (hl.get hj)

/-- After the last round all answers are in place. -/
theorem Answered.all (h : Answered Ready Kept out ans μ ans.length μ') : Seg μ' out ans := by
  simpa using h.answers


/-! ## The routine -/

namespace WantedCore

end WantedCore

variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {W : List (Fin p.N × Fin p.N)} {μ μ' μ'' : ℕ → ℤ}




/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Section 4.4, the offline form: preprocess, then one query for each wanted position

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". Its proof: "The
bound for a set W follows by asking |W| queries." Proof of Theorem 25: "ask one query for each
position of W"; for Corollary 32 the paper uses "the same argument", "With Corollary 31 in place of
Theorem 24".

offline32(N, D, w, U, x, y, wi, wj, out, fr) preprocesses the matrices at x and y (pre31, which uses
the cells from the free pointer fr on) and then asks one query for each of the w positions, whose
rows are at wi and whose columns are at wj; the answers go to out. The arguments are those of the
task `thinTask`. The text `offline32Body`, with the round `offlineAsk32` of its loop, serves all
rational parameters c and θ: they are in the body of the procedure pre31 (`pre31Body`).

A round adds one answer (`offlineAsk32_ends`), with the invariant `Answered` that the offline form
of Theorem 30 uses too, and the routine meets its specification `OfflineSpec32` for all parameters G
(`offline32_meets`).
-/





/-! ## The text -/

/-- The entry (XY)[I, J] for natural numbers I, J (0 outside the matrix). -/
def entryN {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : ℕ) :
    ℤ :=
  if h : I < N ∧ J < N then (X * Y) ⟨I, h.1⟩ ⟨J, h.2⟩ else 0

namespace Offline32

/-- The locals of offline32. The first ten are its arguments: N, D, the number of positions, a bound
that is not used, the addresses of X, of Y, of the rows and of the columns of the wanted positions
and of the output, and the free pointer. Then come the number of the current position and the result
of a call. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Dim : ℕ := 1
@[inherit_doc Size] abbrev Count : ℕ := 2
@[inherit_doc Size] abbrev MatX : ℕ := 4
@[inherit_doc Size] abbrev MatY : ℕ := 5
@[inherit_doc Size] abbrev Rows : ℕ := 6
@[inherit_doc Size] abbrev Cols : ℕ := 7
@[inherit_doc Size] abbrev Out : ℕ := 8
@[inherit_doc Size] abbrev Free : ℕ := 9
@[inherit_doc Size] abbrev Pos : ℕ := 10
@[inherit_doc Size] abbrev Res : ℕ := 11

end Offline32

open Offline32 in
/-- One round of offline32: ask the query for the current position and store its answer. -/
def offlineAsk32 : Stmt :=
  .call Proc.query31 [M (v Rows +' v Pos), M (v Cols +' v Pos), v Size, v Dim, v MatX, v MatY,
    v Free] Res ;;
  .store (v Out +' v Pos) (v Res)

/-! ## What it does -/

/-- **Where the input of offline32 stands**, beyond what `Input31` says: the matrices at aX and aY;
the two lists of indices, which are below N, and the output, all below the free pointer; and the
output meets neither the matrices nor the lists. -/
structure OfflineInput32 {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (aX aY aI aJ out fr : ℕ) (WI WJ : List ℕ) (μ : ℕ → ℤ) : Prop where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  rows : SegN μ aI WI
  cols : SegN μ aJ WJ
  length_eq : WJ.length = WI.length
  rows_lt : ∀ I ∈ WI, I < N
  cols_lt : ∀ J ∈ WJ, J < N
  rows_le : aI + WI.length ≤ fr
  cols_le : aJ + WI.length ≤ fr
  out_le : out + WI.length ≤ fr
  out_matX : Apart out WI.length aX (N * D₀)
  out_matY : Apart out WI.length aY (D₀ * N)
  out_rows : Apart out WI.length aI WI.length
  out_cols : Apart out WI.length aJ WI.length


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Corollaries 26 and 31 in the light language: ⌈a m / b⌉ by counting

Proof of Corollary 26: "Let L := 21m and t := ⌈m/9⌉"; proof of Corollary 31: "with L := ⌈cm⌉ and t
:= ⌈θm⌉". For rational c = a/b the number ⌈a m / b⌉ is found without division: count in steps of b
up to a m. The numbers a and b are constants of the program text.
-/




namespace CeilMul

/-- The locals of ceilMul: the argument m, which the result replaces; the product a m; a counter
that goes up in steps of b; and the number of its steps. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Goal : ℕ := 1
@[inherit_doc Arg] abbrev Reached : ℕ := 2
@[inherit_doc Arg] abbrev Steps : ℕ := 3

end CeilMul

open CeilMul in
/-- ceilMul(m) counts up to a m in steps of b. For m = 0 the result is 0, and the constant a is not
touched (it need not fit in a word then). -/
def ceilMulBody (a b : ℕ) : Stmt :=
  .ite (v Arg =' k 0) .skip
    (.set Goal (k a *' v Arg) ;; .set Reached (k 0) ;; .set Steps (k 0) ;;
      .while (v Reached <' v Goal)
        (.set Reached (v Reached +' k b) ;; .set Steps (v Steps +' k 1)) ;;
      .set Arg (v Steps))

theorem ceilMul_meets {lim : Limits} {P : Program} {pn a b : ℕ} (hb : 1 ≤ b)
    (hP : P[pn]? = some (ceilMulBody a b)) : CeilMulSpec lim P pn a b := by
  intro m μ hw
  refine fun d _ => ⟨ceilMulBody a b, hP, ?_⟩
  unfold ceilMulBody tCeilMul
  -- if m = 0
  refine Ends.iteLast (fun h0 => ?_) (fun h0 => ?_)
  · -- return m
    obtain rfl : m = 0 := by simpa using h0
    exact Ends.skip ⟨by simp [Nat.div_eq_of_lt (by omega : b - 1 < b)], rfl⟩
  · have hm : m ≠ 0 := by simpa using h0
    have hax : a ≤ a * m := Nat.le_mul_of_pos_right a (by omega)
    have hxZ : (a : ℤ) * m = (a * m : ℕ) := by push_cast; rfl
    generalize a * m = x at hw hax hxZ ⊢
    have hlt : ∀ i, i < (x + b - 1) / b ↔ i * b < x := fun i => Nat.lt_ceilDiv_iff hb
    have hnx : (x + b - 1) / b ≤ x := by
      by_contra hc
      have := (hlt x).1 (by omega)
      have := Nat.le_mul_of_pos_right x hb
      omega
    generalize (x + b - 1) / b = n at hlt hnx ⊢
    -- am := a * m ; c := 0 ; steps := 0
    light_set x using hxZ
    light_set 0
    light_set 0
    -- while c < am: c := c + b ; steps := steps + 1.  Before round i, c = i b and steps = i.
    refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [m, x, ((i * b : ℕ) : ℤ), i], μ⟩) n
      (by simp) ?round ?done (hT := le_rfl))
    case round =>
      rintro i _ hi rfl
      have hbi := (hlt i).1 hi
      rw [Nat.succ_mul]
      generalize i * b = c at hbi ⊢
      exact ⟨by light_side, by simp; omega, by light_side, by simp [update_frame_setLocal]⟩
    case done =>
      rintro _ rfl
      have hbn := mt (hlt n).2 (lt_irrefl n)
      generalize n * b = c at hbn ⊢
      -- return steps
      exact ⟨by light_side, by simp; omega, Ends.setTo (n : ℤ) ⟨rfl, rfl⟩⟩



/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Padding X with zero columns

Proof of Corollary 26: "pad the inner dimension to 4^m < 4D with zero columns of X". Row by row: a
copy of the row and a fill with zeros. The invariant `PadX.Rows` says that the first i rows of the
padded matrix have been written; `PadX.Rows.succ` is what a round does to the memory, and
`padX_meets` the specification.
-/




namespace PadX

/-- The local variables of padX: the arguments N, D, D', aX, aX', the row, and a result that is not
used. -/
abbrev Height : ℕ := 0
@[inherit_doc Height] abbrev Width : ℕ := 1
@[inherit_doc Height] abbrev Padded : ℕ := 2
@[inherit_doc Height] abbrev Source : ℕ := 3
@[inherit_doc Height] abbrev Dest : ℕ := 4
@[inherit_doc Height] abbrev Row : ℕ := 5
@[inherit_doc Height] abbrev Unused : ℕ := 6

end PadX

open PadX in
/-- padX(N, D, D', aX, aX'): for each row i, copy its D entries from aX + i D to aX' + i D', and
fill the D' - D cells behind them with zeros. -/
def padXBody : Stmt :=
  .for Row (v Height) (
    .call Proc.copy [v Source +' v Row *' v Width, v Dest +' v Row *' v Padded, v Width] Unused ;;
    .call Proc.fill [v Dest +' v Row *' v Padded +' v Width, v Padded -' v Width, k 0] Unused)

namespace PadX

variable {N D₀ D' aX aX' i : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ} {μ μ' μ₁ μ₂ : ℕ → ℤ}

/-- The memory before row i: the first i rows of the padded matrix stand at aX', and no cell outside
them has changed. -/
def Rows (μ : ℕ → ℤ) (aX' D' : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ (r : Fin N) (j : Fin D'), (r : ℕ) < i → μ' (aX' + r * D' + j) = padInnerCols D' X r j) ∧
    SameOutside μ μ' aX' (i * D')

/-- A round: row i of X has been copied, and zeros have been written behind it. -/
theorem Rows.succ (h : Rows μ aX' D' X i μ') (hX : MatAt μ aX X) (hsep : aX + N * D₀ ≤ aX')
    (hi : i < N) (hcopy : ∀ j < D₀, μ₁ (aX' + i * D' + j) = μ' (aX + i * D₀ + j))
    (hout₁ : SameOutside μ' μ₁ (aX' + i * D') D₀)
    (hfill : ∀ j < D' - D₀, μ₂ (aX' + i * D' + D₀ + j) = 0)
    (hout₂ : SameOutside μ₁ μ₂ (aX' + i * D' + D₀) (D' - D₀)) (hDD : D₀ ≤ D') :
    Rows μ aX' D' X (i + 1) μ₂ := by
  have : i * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul hi le_rfl
  refine ⟨fun r j hr => ?_, fun b hb => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hlt | heq
    · -- an earlier row lies below the cells that the round has written
      have := Nat.mul_add_lt_mul hlt j.isLt
      rw [hout₂ _ (.inl (by omega)), hout₁ _ (.inl (by omega))]
      exact h.1 r j hlt
    · by_cases hj : (j : ℕ) < D₀
      · -- an entry of X, which is as at the start
        rw [heq, hout₂ _ (.inl (by omega)), hcopy _ hj, h.2 _ (.inl (by omega)), padInnerCols,
          dif_pos hj, ← heq]
        exact hX r ⟨j, hj⟩
      · -- a zero
        have hcell : aX' + (r : ℕ) * D' + (j : ℕ) = aX' + i * D' + D₀ + ((j : ℕ) - D₀) := by
          rw [heq]; omega
        rw [hcell, hfill _ (by have := j.isLt; omega), padInnerCols, dif_neg hj]
  · rw [Nat.succ_mul] at hb
    rw [hout₂ b (by omega), hout₁ b (by omega), h.2 b (by omega)]

end PadX

open PadX in
theorem padX_meets {lim : Limits} {P : Program} (hP : P[Proc.padX]? = some padXBody)
    (hcopy : CopySpec lim P) (hfill : FillSpec lim P) (hstd : Std lim) : PadXSpec lim P := by
  intro N D₀ D' aX aX' X μ hDD hD1 hX hsep hsp
  refine fun d hd => ⟨padXBody, hP, ?_⟩
  have := hstd.space_le
  have := hstd.const_le
  have : N ≤ N * D' := Nat.le_mul_of_pos_right _ hD1
  have hsub : (D' : ℤ) - D₀ = ((D' - D₀ : ℕ) : ℤ) := (Nat.cast_sub hDD).symm
  unfold padXBody tPadX
  -- for i < N
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame [N, D₀, D', aX, aX', i, r], μ'⟩ ∧ Rows μ aX' D' X i μ') N (16 * D' + 60)
    ?start ?round ?done ?bound
  case start =>
    exact ⟨0, μ, by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl,
      fun r j hr => absurd hr (Nat.not_lt_zero _), fun _ _ => rfl⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨r, μ', rfl, hrows, hout⟩
    exact ⟨fun r j => hrows r j r.isLt, hout⟩
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hrows⟩
    -- row i of X and row i of the padded matrix lie within their arrays
    have : i * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul hi le_rfl
    have : i * D' + D' ≤ N * D' := Nat.mul_add_le_mul hi le_rfl
    -- copy(aX + i D, aX' + i D', D)
    refine Ends.callToThen (hcopy (aX + i * D₀) (aX' + i * D') D₀ μ' (by omega) (by omega)
      (by omega) (.inl (by omega)) _ (by omega)) ?_ (hT := by simp [tCopy]; omega)
    rintro - μ₁ ⟨hc, hout₁⟩
    -- fill(aX' + i D' + D, D' - D, 0)
    refine Ends.callTo (hfill (aX' + i * D' + D₀) (D' - D₀) 0 μ₁ (by omega) (by omega) _
      (by omega)) ?_ (by light_side [hsub]) (hT := by simp [tCopy, tFill]; omega)
    rintro r' μ₂ ⟨hf, hout₂⟩
    exact ⟨by simp, r', μ₂, by rw [update_frame_setLocal]; rfl,
      hrows.succ hX hsep hi hc hout₁ hf hout₂ hDD⟩



/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# An entry of the product as an inner product

Proof of Corollary 26: "(For m < 60, D is bounded by a constant, and the corollary holds
trivially.)"; proof of Corollary 31: "for smaller m the corollary again holds trivially". In the
programs a query then computes an inner product, of a bounded number D of summands. The routine adds
the D products X[I, s] Y[s, J]. `ipPart` is the sum of the first s of them, with its recursion
(`ipPart_succ`), its bound (`abs_ipPart_le`) and its last value (`ipPart_full`); `ipAt_meets` is the
specification.
-/



open Finset

namespace IpAt

/-- The locals of ipAt. The first six are its arguments I, J, N, D, aX, aY; the answer replaces I.
Then come the index s of the summand, the sum, the address of row I of X, and the address of Y[0,
J]. -/
abbrev Row : ℕ := 0
@[inherit_doc Row] abbrev Col : ℕ := 1
@[inherit_doc Row] abbrev Size : ℕ := 2
@[inherit_doc Row] abbrev Dim : ℕ := 3
@[inherit_doc Row] abbrev MatX : ℕ := 4
@[inherit_doc Row] abbrev MatY : ℕ := 5
@[inherit_doc Row] abbrev Pos : ℕ := 6
@[inherit_doc Row] abbrev Sum : ℕ := 7
@[inherit_doc Row] abbrev RowAt : ℕ := 8
@[inherit_doc Row] abbrev ColAt : ℕ := 9

end IpAt

open IpAt in
/-- ipAt(I, J, N, D, aX, aY): the inner product of row I of X and column J of Y. -/
def ipAtBody : Stmt :=
  .set Pos (k 0) ;; .set Sum (k 0) ;;
  .set RowAt (v MatX +' v Row *' v Dim) ;; .set ColAt (v MatY +' v Col) ;;
  .while (v Pos <' v Dim)
    (.set Sum (v Sum +' M (v RowAt +' v Pos) *' M (v ColAt +' v Pos *' v Size)) ;;
      .set Pos (v Pos +' k 1)) ;;
  .set Row (v Sum)

variable {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : Fin N)

/-- The first s summands of the inner product. -/
def ipPart (s : ℕ) : ℤ := ∑ i ∈ range s, if h : i < D₀ then X I ⟨i, h⟩ * Y ⟨i, h⟩ J else 0

theorem ipPart_full : ipPart X Y I J D₀ = (X * Y) I J := by
  rw [Matrix.mul_apply, ipPart, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by simp

theorem ipPart_succ {s : ℕ} (hs : s < D₀) :
    ipPart X Y I J (s + 1) = ipPart X Y I J s + X I ⟨s, hs⟩ * Y ⟨s, hs⟩ J := by
  rw [ipPart, Finset.sum_range_succ, dif_pos hs]
  rfl

variable {X Y}

theorem abs_mul_entry_le {U : ℤ} (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (s : Fin D₀) :
    |X I s * Y s J| ≤ U * U := by
  rw [abs_mul]
  exact mul_le_mul (hX _ _) (hY _ _) (abs_nonneg _) (le_trans (abs_nonneg _) (hX I s))

theorem abs_ipPart_le {U : ℤ} (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) :
    ∀ s ≤ D₀, |ipPart X Y I J s| ≤ s * (U * U)
  | 0, _ => by simp [ipPart]
  | s + 1, hs => by
    rw [ipPart_succ X Y I J hs]
    refine (abs_add_le _ _).trans ?_
    have := abs_ipPart_le hX hY s (by omega)
    have := abs_mul_entry_le I J hX hY ⟨s, hs⟩
    push_cast
    linarith


theorem ipAt_meets {lim : Limits} {P : Program} (hP : P[Proc.ipAt]? = some ipAtBody)
    (hstd : Std lim) : IpAtSpec lim P := by
  intro N D₀ aX aY X Y U μ I J hD hmX hmY hX hY sX sY hU
  refine fun d _ => ⟨ipAtBody, hP, ?_⟩
  have hw := hstd.space_le
  have h100 := hstd.const_le
  have hrow : (I : ℕ) * D₀ + D₀ ≤ N * D₀ := Nat.mul_add_le_mul I.isLt le_rfl
  have hcol : (J : ℕ) < N := J.isLt
  have hN : N ≤ D₀ * N := Nat.le_mul_of_pos_left _ hD
  -- every partial sum and every product fits in a word
  have hfits : ∀ s ≤ D₀, |ipPart X Y I J s| ≤ lim.word := fun s hs =>
    (abs_ipPart_le I J hX hY s hs).trans (le_trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hs)
        (le_trans (abs_nonneg _) (abs_mul_entry_le I J hX hY ⟨0, hD⟩))) hU)
  have hprod : ∀ s : Fin D₀, |X I s * Y s J| ≤ lim.word := fun s =>
    (abs_mul_entry_le I J hX hY s).trans (le_trans (le_mul_of_one_le_left
      (le_trans (abs_nonneg _) (abs_mul_entry_le I J hX hY s)) (by exact_mod_cast hD)) hU)
  unfold ipAtBody tIpAt
  -- s := 0 ; sum := 0 ; row := aX + I * D ; col := aY + J
  light_set 0
  light_set 0
  light_set (aX + (I : ℕ) * D₀ : ℕ)
  light_set (aY + (J : ℕ) : ℕ)
  -- while s < D: sum := sum + mem[row + s] * mem[col + s * N] ; s := s + 1
  refine Ends.next _ (Ends.whileBlock (fun s σ => σ = ⟨frame [(I : ℕ), (J : ℕ), N, D₀, aX, aY, s,
      ipPart X Y I J s, ((aX + (I : ℕ) * D₀ : ℕ) : ℤ), ((aY + (J : ℕ) : ℕ) : ℤ)], μ⟩) D₀
    (by simp [ipPart]) ?round ?done (hT := le_rfl))
  case round =>
    rintro s _ hs rfl
    have hcell : s * N + N ≤ D₀ * N := Nat.mul_add_le_mul hs le_rfl
    have hx : μ (aX + (I : ℕ) * D₀ + s) = X I ⟨s, hs⟩ := hmX I ⟨s, hs⟩
    have hy : μ (aY + (J : ℕ) + s * N) = Y ⟨s, hs⟩ J := by
      rw [← hmY ⟨s, hs⟩ J]
      congr 1
      change aY + (J : ℕ) + s * N = aY + s * N + (J : ℕ)
      omega
    have haddrX : ((aX : ℤ) + (I : ℕ) * D₀ + s).toNat = aX + (I : ℕ) * D₀ + s := by
      rw [← Int.toNat_natCast (aX + (I : ℕ) * D₀ + s)]; push_cast; rfl
    have haddrY : ((aY : ℤ) + (J : ℕ) + s * N).toNat = aY + (J : ℕ) + s * N := by
      rw [← Int.toNat_natCast (aY + (J : ℕ) + s * N)]; push_cast; rfl
    have hsum := abs_le.1 (hfits (s + 1) hs)
    have hxy := abs_le.1 (hprod ⟨s, hs⟩)
    rw [ipPart_succ X Y I J hs] at hsum ⊢
    generalize ipPart X Y I J s = S at hsum ⊢
    generalize X I ⟨s, hs⟩ = x at hx hsum hxy ⊢
    generalize Y ⟨s, hs⟩ J = y at hy hsum hxy ⊢
    exact ⟨by light_side, by simp; omega, by light_side [haddrX, haddrY, hx, hy],
      by simp [update_frame_setLocal, haddrX, haddrY, hx, hy]⟩
  case done =>
    rintro _ rfl
    -- return sum
    exact ⟨by light_side, by simp, Ends.setTo (ipPart X Y I J D₀) ⟨ipPart_full X Y I J, rfl⟩⟩



/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Corollaries 26, 31 and 32: the concrete program for given parameters

program31 G = base58 (Theorem 5's and Theorem 30's procedures, numbers 0 to 57) followed by the
procedures 58 to 73 of Section 4.4 (`procs31`): copying, filling, m = ⌈log₄ D⌉, padding and the
inner product; the preprocessing pre31Body G at 64 and the query; their main procedures; the offline
routine and its main procedure; the solver of Corollary 26 for all instances with its test; and the
two procedures for L = ⌈am/b⌉ and t = ⌈pm/q⌉ at 72 and 73. The specifications of the preprocessing,
the query and the offline routine hold for it, for all limits, without hypotheses. At the parameters
of Corollary 26 it is `program26`.

With the two end theorems for light programs and the compiler this gives the two statements about
the word RAM from which Corollaries 26, 31 and 32 follow: on every domain of inputs, and for all
bounds that dominate the two costs of Theorem 30 at the parameters G (`CostsWithin`), the compiled
program is a data structure (`isDataStructure_of_costsWithin`) and solves the offline problem
(`solves_of_costsWithin`).
-/



open ThreeSumApsp.WordRam

/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/

def procs31 (G : RatParams) : List Stmt :=
  [copyBody, fillBody, log4Body, .skip, padXBody, ipAtBody, .skip, query31Body,
    .skip, .skip, .skip, .skip, .skip,
    .skip, ceilMulBody G.a G.b, ceilMulBody G.p G.q]

/-- The program for the parameters G. -/
def program31 (G : RatParams) : Program := base58 ++ procs31 G

/-- The routines stand at their numbers. -/
theorem program31_at (G : RatParams) (n : ℕ) {body : Stmt} (hn : 58 ≤ n := by norm_num)
    (h : (procs31 G)[n - 58]? = some body := by rfl) : (program31 G)[n]? = some body := by
  rw [program31, List.getElem?_append_right (by rw [length_base58]; exact hn), length_base58]
  exact h

/-! ## The program on the word RAM -/



/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Corollary 26, the offline form, on all instances

Corollary 26 is about matrices with N ≥ D^18. A solver that other procedures call has to be right on
every instance. allInstances26(N, D, w, U, x, y, wi, wj, out, fr) tests whether D^18 ≤ N, calls the
offline routine offline32 if so and the brute force if not. The texts are `allInstances26Body` and
`regimeTest26Body`.

* *The routine.* It solves the task `thinTask` on every instance, within the time
  `allInstancesTime26` and the need `allInstancesNeed26` (`allInstances26_solves`). It tests whether
  D^18 ≤ N (`regimeTest26_meets`). In that regime it calls the offline routine of Corollary 26,
  whose demands on the limits are covered by the need (`lim31_of_need`, `offline32_meets_thinTask`);
  outside it calls the brute force.
* *The time in the regime.* For N ≥ D^18 the time is O(w D^{0.437} + N²/D^{0.063}), the bound of
  Corollary 26: the time of the offline routine is at most a constant times tp + w tq for all bounds
  that dominate the two costs of Theorem 30 (`exists_tOffline32_le`), and in the regime the two
  bounds of Corollary 26 do (`regime26`).
* *The need is polynomial in the parameters.* Every summand of the need is a numeral times a product
  of at most 20 factors N + 1, D and U. With Q = (N + 1) (D + 1) (w + 1) (U + 1) each factor is at
  most Q, so each product is at most Q^20 (`le_pow_twenty`). So the largest number, the cells and
  the levels of calls are at most 2^11 Q^20 (`word_le`, `cells_le`, `depth_le`).
-/




/-! ## Time and need -/

/-! ## The test -/

/-! ## The limits -/

section need

variable {lim : Limits} {N D₀ w U fr d : ℕ}

end need

/-! ## The matrices of an instance -/

/-- The first matrix of an instance. -/
def thinMX (x : ThinInst) : Matrix (Fin x.N) (Fin x.D) ℤ := fun i j => x.X.getD (i * x.D + j) 0

/-- The second matrix of an instance. -/
def thinMY (x : ThinInst) : Matrix (Fin x.D) (Fin x.N) ℤ := fun i j => x.Y.getD (i * x.N + j) 0

theorem matAt_thinMX {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) : MatAt μ x.x
    (thinMX x) := by
  intro i j
  have hlt : (i : ℕ) * x.D + j < x.X.length := by
    rw [h.lenX]
    have := Nat.mul_add_le_mul i.isLt (le_refl x.D)
    have := j.isLt
    omega
  rw [Nat.add_assoc, h.segX.getD hlt 0]
  rfl

theorem matAt_thinMY {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) : MatAt μ x.y
    (thinMY x) := by
  intro i j
  have hlt : (i : ℕ) * x.N + j < x.Y.length := by
    rw [h.lenY]
    have := Nat.mul_add_le_mul i.isLt (le_refl x.N)
    have := j.isLt
    omega
  rw [Nat.add_assoc, h.segY.getD hlt 0]
  rfl

/-- The entry of the product of the two matrices is the entry that the task asks for. -/
theorem entryN_thin (x : ThinInst) {I J : ℕ} (hI : I < x.N) (hJ : J < x.N) :
    entryN (thinMX x) (thinMY x) I J = thinEntry x.N x.D x.X x.Y I J := by
  rw [entryN, dif_pos ⟨hI, hJ⟩, Matrix.mul_apply, thinEntry, List.sum_map_range, Finset.sum_range]
  rfl

/-! ## The routine -/

/-- The answers of the offline routine are those that the task asks for. -/
theorem map_entryN_thin {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) :
    (x.WI.zip x.WJ).map (fun q => entryN (thinMX x) (thinMY x) q.1 q.2)
      = thinOut x.N x.D x.X x.Y x.WI x.WJ :=
  List.map_congr_left fun _ hq =>
    entryN_thin x (h.ltWI _ (List.of_mem_zip hq).1) (h.ltWJ _ (List.of_mem_zip hq).2)

/-! ## The time in the regime -/

/-! ## The need is polynomial in the parameters -/

section summands

variable {N D U Q : ℕ}

end summands

end Light.Sec4
