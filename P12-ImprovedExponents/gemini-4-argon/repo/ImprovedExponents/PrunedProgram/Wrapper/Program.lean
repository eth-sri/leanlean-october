module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Sec4.Corollary31
public import ThreeSumApsp.Sec4.Corollary31.RationalParameters
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program
public import ThreeSumApsp.Sec4.Table2.LogBounds
public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Log
public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
public import ImprovedExponents.PrunedProgram.Pre.Defs
public import ThreeSumApsp.Programs.Sec4.Theorem30.Directory
public import ThreeSumApsp.Programs.Sec4.Theorem30.Program
public import ImprovedExponents.PrunedProgram.Tiles.FillList
public import ImprovedExponents.PrunedProgram.Tiles.Tile
public import ImprovedExponents.PrunedProgram.Tiles.AllTiles
public import ImprovedExponents.PrunedProgram.Query.QuerySum
public import ImprovedExponents.PrunedProgram.Shared.Stage

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Corollaries 31 and 32: the parameters of the program, and where its costs are bounded

For real c > 10, 0 < θ < 0.9 and ε < R_c(γ) there are parameters G for the program text (rational c'
and θ', a threshold m₀) and a constant C such that on every instance with 1 ≤ D ≤ N^ε and with m ≥
m₀ the costs of Theorem 30 at these parameters are at most C times

    Tp = N² (log D + 1)²/D^γ     and     Tq = D^q (log D + 1),

γ and q being those of c and θ (`exists_ratParams`).

The rational parameters come from `exists_rat_params` and the costs at them from
`Corollary31.costs`. What is left is to compare the bounds: γ(c', θ') ≥ γ(c, θ) and q(θ') ≤ q(θ)
make the bounds at the rational parameters smaller (`le_preBound31`, `le_queryBound31`), and both
bounds are at least 1 (`one_le_preBound31`, `one_le_queryBound31`), so that additive constants can
be absorbed.
-/


open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-- The bound on the preprocessing, N² (log D + 1)²/D^γ. -/
noncomputable def preBound31 (γ : ℝ) (N D₀ : ℕ) : ℝ :=
  (N : ℝ) ^ 2 * (Real.log D₀ + 1) ^ 2 / (D₀ : ℝ) ^ γ
/-- The bound on a query, D^q (log D + 1); the summand 1 makes it at least 1 at D = 1. -/
noncomputable def queryBound31 (q : ℝ) (D₀ : ℕ) : ℝ := (D₀ : ℝ) ^ q * (Real.log D₀ + 1)

section bounds

variable {N D₀ : ℕ}

end bounds

end Light.Sec4





/-!
# The time of the offline routine of Section 4, as one statement

The offline routine `offline32` of the upstream program `program31 G` preprocesses and then answers
one query for each wanted position. Its parameters `G : RatParams` are in the program text: the
ratios `c = a/b` and `θ = p/q` and the threshold `m₀` below which it computes inner products.

`OfflineWithinT t ε γ q` says that a routine with the running time `t N D w` takes, on every
instance with `1 ≤ D ≤ N^ε`, at most a constant times

  `N² (log D + 1)²/D^γ + w D^q (log D + 1)`

steps, `w` being the number of wanted positions; `OfflineWithin G ε γ q` is this for the time of
`offline32`. This is the only fact about running times that the solver built on a routine needs
(`ImprovedExponents.Pipeline.ThinClaim`).

Upstream proves it with the paper's exponent `γ = θ ln(1/ρ_c)/ln 4` (`offlineWithin_gammaOf`, a
restatement of `Light.Sec4.exists_ratParams` for parameters that are given rather than chosen).
-/

namespace ImprovedExponents

open Light Light.Sec4

/-- A routine with the running time `t N D w` takes at most a constant times
`N² (log D + 1)²/D^γ + w D^q (log D + 1)` steps (400 further steps included) on every instance with
`1 ≤ D ≤ N^ε`. -/
def OfflineWithinT (t : ℕ → ℕ → ℕ → ℕ) (ε γ q : ℝ) : Prop :=
  ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
    (t N D₀ w : ℝ) + 400 ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀)

section bounds

variable {N D₀ : ℕ}

/-- `D ≤ N^ε` with `ε γ ≤ 1` gives `D^γ ≤ N²`. -/
theorem rpow_le_sq {ε γ : ℝ} (hN : 1 ≤ N) (hγ : 0 ≤ γ) (hεγ : ε * γ ≤ 1)
    (h : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : (D₀ : ℝ) ^ γ ≤ (N : ℝ) ^ 2 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc (D₀ : ℝ) ^ γ ≤ ((N : ℝ) ^ ε) ^ γ := Real.rpow_le_rpow (by positivity) h hγ
    _ = (N : ℝ) ^ (ε * γ) := by rw [← Real.rpow_mul (by positivity)]
    _ ≤ (N : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
    _ = (N : ℝ) ^ 2 := by norm_cast

/-- The bound on the preprocessing is at least 1 if `D^γ ≤ N²`. -/
theorem one_le_preBound31 {γ : ℝ} (hD : 1 ≤ D₀) (h : (D₀ : ℝ) ^ γ ≤ (N : ℝ) ^ 2) :
    1 ≤ preBound31 γ N D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have := Real.log_nonneg hDR
  unfold preBound31
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _), one_mul]
  exact h.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith)))

/-- The bound on a query is at least 1. -/
theorem one_le_queryBound31 {q : ℝ} (hD : 1 ≤ D₀) (hq : 0 ≤ q) : 1 ≤ queryBound31 q D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have := Real.log_nonneg hDR
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hDR hq) (by linarith)

theorem le_preBound31 {γ : ℝ} (hD : 1 ≤ D₀) :
    (N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ γ ≤ preBound31 γ N D₀ := by
  have hDR : (1 : ℝ) ≤ D₀ := by exact_mod_cast hD
  have hlog := Real.log_nonneg hDR
  have hsq : Real.log (D₀ : ℝ) ^ 2 ≤ (Real.log D₀ + 1) ^ 2 := pow_le_pow_left₀ hlog (by linarith) 2
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)

theorem le_queryBound31 {q : ℝ} (hD : 1 ≤ D₀) :
    (D₀ : ℝ) ^ q * Real.log (D₀ : ℝ) ≤ queryBound31 q D₀ :=
  mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end bounds


/-!
# A thin-product solver at any parameters of the program

Upstream's solver for Corollary 26 is the procedure `allInstances26` of the program
`program31 ratParams26`: it tests whether `D^18 ≤ N`, calls the offline routine `offline32` if so
and the brute force if not (`Light.Sec4.allInstances26_solves`). The same three procedures are in
`program31 G` for every `G : RatParams`. This file redoes the upstream proof for an arbitrary `G`
(it follows `ThreeSumApsp/Programs/Sec4/Corollary26/AllInstances.lean` and `Claim.lean` line by
line; several lemmas there are private and are repeated here).

The solver `allBody` is generic in its two callees:

* the regime test (`RegimeTest`): a procedure that returns 1 on the instances `(N, D)` of a regime
  `Reg N D` and 0 on the others, with its time and the largest number it forms. Upstream's test
  `D^18 ≤ N` is the instance `regime18`; `ImprovedExponents.Pipeline.RegimeRS` adds the test
  `D^r ≤ N^s`;
* the offline routine (`OfflineRoutine`): a procedure that solves the thin product on the
  instances `Ok N D`, with its time and its need. Upstream's routine `offline32` at the parameters
  `G` is the instance `offline32Routine G`; `ImprovedExponents.PrunedProgram` adds the routine with
  the pruned encoder.

A solver has to be right on every instance, so the whole regime of the test must lie where the
routine is specified. For `offline32` this means that the hypotheses of Theorem 30 hold from the
threshold `m₀` on: this is `FitsR R G` (`Fits18 G` for the test of the program). It limits the
ratio `c = a/b` (the tile `√K N₀` must fit into `N`).

The result is `thinClaimR_of_offlineWithin`: if the offline routine stays within its two bounds on
the instances with `D ≤ N^ε` (`OfflineWithinT` of its time; `OfflineWithin` for `offline32`), and
these lie in the regime, then the thin product is solved, in the sense of the time model
`lightModel`, by one procedure whose time on these instances is at most a constant times
`w D^q (log D + 1) + N² (log D + 1)²/D^γ` (`ThinClaim`). `thinClaim_of_offlineWithin` is the case
of the program's test and routine, with `ε ≤ 1/18`.
-/


open ThreeSumApsp.Spec

/-! ## The statement -/

/-- A time claim for the thin matrix product: one solver for all instances whose time on the
instances with `D ≤ N^ε` is at most a constant times `w D^q (log D + 1) + N² (log D + 1)²/D^γ`,
for `w` wanted positions. (Compare `Claim.Corollary_26_wanted`.) -/
def ThinClaim (M : DetTimeModel) (ε γ q : ℝ) : Prop :=
  ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ → ℝ), M.thinProduct T ∧
    ∀ (N D w : ℕ) (u : ℝ), 1 ≤ N → 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ ε →
      T N D w u ≤ C * (preBound31 γ N D + (w : ℝ) * queryBound31 q D)

def allBody (test off : ℕ) : Stmt :=
  .call test [v 0, v 1] 10 ;;
  .ite (k 0 <' v 10)
    (.call off [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)
    (.call Sec2.pThinBrute [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)

theorem ratParams_L_le_mul (G : RatParams) (m : ℕ) : G.L m ≤ G.a * m := by
  unfold RatParams.L
  have hb := G.hb
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have : G.a * m ≤ G.b * (G.a * m) := Nat.le_mul_of_pos_left _ (by omega)
  omega

def offline32Need (G : RatParams) (N D U : ℕ) : Need :=
  ⟨1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U)
      + 7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5
      + (G.a * (4 * D) + G.p * (4 * D) + G.b + G.q + G.m₀),
    4 + N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4, G.a * (4 * D) + 12⟩

section need

variable {lim : Limits} {G : RatParams} {N D₀ U fr d : ℕ}

theorem fits_of_need (ok : (offline32Need G N D₀ U).Ok lim fr d) {n : ℕ}
    (hn : n ≤ 1000 + 100 * D₀ + N * D₀ + D₀ * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U) +
      7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5
        + (G.a * (4 * D₀) + G.p * (4 * D₀) + G.b + G.q + G.m₀)) : (n : ℤ) ≤ lim.word :=
  le_trans (by exact_mod_cast hn) ok.word

theorem top_le_of_need (hD : 1 ≤ D₀) (H : Hyp30 (parOf G N D₀) (switchOf31 G D₀))
    (ok : (offline32Need G N D₀ U).Ok lim fr d) :
    top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) ≤ lim.space := by
  have : fr + (4 + N + 8 * (N * D₀) + 222 * ((N + 1) ^ 5) ^ 4) ≤ lim.space := ok.cells
  have : top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) - blockAt N D₀ fr
      ≤ 222 * ((N + 1) ^ 5) ^ 4 := top_sub_le_pow H (below H) _
  have : N * D (logFour D₀) ≤ 4 * (N * D₀) :=
    (Nat.mul_le_mul_left N (Nat.pow_clog_le_mul (b := 4) (by norm_num) hD)).trans_eq (by ring)
  have : blockAt N D₀ fr = fr + 3 + N * D (logFour D₀) + N * D (logFour D₀) := rfl
  omega

theorem lim30_of_below {p : Sec2.Par} {t b0 B : ℕ} (hB : Below p t B) (std : Std lim)
    (hspace : top p t b0 ≤ lim.space)
    (fits : ∀ n : ℕ, n ≤ B ^ 3 * (U * U) + 7 * (B * U) + 10 * B → (n : ℤ) ≤ lim.word) :
    Lim30 lim p t b0 (U : ℤ) := by
  have := hB.T
  have := hB.S7
  have := hB.tenm
  have hvalue : 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ B ^ 3 * (U * U) :=
    calc 10 ^ p.m * ((7 ^ p.L * U) * (7 ^ p.L * U)) ≤ B * ((B * U) * (B * U)) := by gcongr
      _ = B ^ 3 * (U * U) := by ring
  have henc : 7 ^ (p.L + 1) * U ≤ 7 * (B * U) :=
    calc 7 ^ (p.L + 1) * U = 7 * (7 ^ p.L * U) := by ring
      _ ≤ 7 * (B * U) := by gcongr
  have hpow : 10 ^ (p.L + 1) ≤ 10 * B :=
    calc 10 ^ (p.L + 1) = 10 * 10 ^ p.L := by ring
      _ ≤ 10 * B := by gcongr
  exact {
    std := std
    space := hspace
    value := by exact_mod_cast fits _ (hvalue.trans (by omega))
    enc := by exact_mod_cast fits _ (henc.trans (by omega))
    pow := fits _ (hpow.trans (by omega)) }

theorem lim31_of_need (hD : 1 ≤ D₀)
    (hfit : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀))
    (ok : (offline32Need G N D₀ U).Ok lim fr d) : Lim31 lim G N D₀ fr (U : ℤ) := by
  have : fr + (4 + N + 8 * (N * D₀) + 222 * ((N + 1) ^ 5) ^ 4) ≤ lim.space := ok.cells
  have fits {n : ℕ} := fits_of_need ok (n := n)
  have : 4 ^ logFour D₀ ≤ 4 * D₀ := Nat.pow_clog_le_mul (b := 4) (by norm_num) hD
  have hm4 : logFour D₀ ≤ 4 * D₀ := logFour_le_four_mul hD
  have : G.a * logFour D₀ ≤ G.a * (4 * D₀) := Nat.mul_le_mul_left _ hm4
  have : G.p * logFour D₀ ≤ G.p * (4 * D₀) := Nat.mul_le_mul_left _ hm4
  have std : Std lim := ⟨ok.space, by exact_mod_cast fits (n := 100) (by omega)⟩
  have large (hm : G.m₀ ≤ logFour D₀) : Lim30 lim (parOf G N D₀) (switchOf31 G D₀)
      (blockAt N D₀ fr) (U : ℤ) :=
    have H := hfit hm
    lim30_of_below (B := (N + 1) ^ 5) (below H) std (top_le_of_need hD H ok)
      fun n hn => fits (hn.trans (by omega))
  exact {
    std := std
    space := by
      unfold structEnd
      split_ifs with h
      · omega
      · exact (large (not_lt.mp h)).space
    pow := fits (by omega)
    mword := fits (by omega)
    m0word := fits (n := G.m₀) (by omega)
    ip := by exact_mod_cast fits (n := D₀ * (U * U)) (by omega)
    large := large }

end need

theorem OfflineWithinT.add_const {t : ℕ → ℕ → ℕ → ℕ} {ε γ q : ℝ} (h : OfflineWithinT t ε γ q)
    (K : ℕ) : ∃ A : ℝ, ∀ N D₀ w : ℕ, 1 ≤ N → 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ ε →
      (t N D₀ w : ℝ) + 400 + K ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A * (1 + K / 400), fun N D₀ w hN hD hDN => ?_⟩
  have := hA N D₀ w hN hD hDN
  have : (0 : ℝ) ≤ t N D₀ w := by positivity
  have : (0 : ℝ) ≤ K := by positivity
  have hB : 400 ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀) := by linarith
  calc (t N D₀ w : ℝ) + 400 + K
      ≤ A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀)
        + K / 400 * (A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀)) := by
        have : K ≤ K / 400 * (A * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀)) := by
          calc (K : ℝ) = K / 400 * 400 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
        linarith
    _ = A * (1 + K / 400) * (preBound31 γ N D₀ + (w : ℝ) * queryBound31 q D₀) := by ring

theorem pow_le_pow_of_le_rpow {N D₀ r : ℕ} {ε : ℝ} (hr : 1 ≤ r) (hε : ε ≤ 1 / (r : ℝ))
    (hN : 1 ≤ N) (hDN : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : D₀ ^ r ≤ N := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h : ((D₀ : ℝ)) ^ r ≤ (N : ℝ) :=
    calc ((D₀ : ℝ)) ^ r ≤ ((N : ℝ) ^ ε) ^ r := pow_le_pow_left₀ (by positivity) hDN r
      _ = (N : ℝ) ^ (ε * r) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR (by rwa [le_div_iff₀ hrR] at hε)
      _ = (N : ℝ) := Real.rpow_one _
  exact_mod_cast h


/-!
# A regime test with a rational exponent

The solver of `ImprovedExponents.Pipeline.ThinClaim` is generic in its regime test. Upstream's test
decides `D^18 ≤ N`. This file adds, for natural numbers `r` and `s`, a procedure `testRS r s` that
decides `D^r ≤ N^s`: it computes `N^s` by a loop and calls upstream's `powLt` (which computes `D^r`
without ever exceeding its bound). The three procedures `powLt`, `testRS r s` and the solver that
calls it (`allRSBody`) are appended to `program31 G` (`programRS G r s`).

The result is `thinClaimRS_of_offlineWithin`: the thin product is solved within the bounds of the
offline routine on the instances with `D ≤ N^ε`, for `ε ≤ s/r`, if the tile fits in the whole
regime `D^r ≤ N^s` (`FitsRS G r s`). `thinClaimRS_of_offlineWithinT` is the same for any offline
routine (`OfflineRoutine`) in a program that begins with `programRS G r s`; it serves the pruned
routine of `ImprovedExponents.PrunedProgram`, whose solver is `allBody Proc.testRS Proc.offline32P`.
-/


open Light.Sec3

/-! ## The procedures -/

namespace Proc

/-- The number of `powLt` in `programRS`. -/
abbrev powRS : ℕ := 74
/-- The number of `testRS r s` in `programRS`. -/
abbrev testRS : ℕ := 75

end Proc

def testRSBody (r : ℕ) : Stmt :=
  .call Proc.powRS [v 1, k r, v 0 +' k 1] 0

def allRSBody : Stmt := .skip

def programRS (G : RatParams) (r : ℕ) : Program :=
  program31 G ++ [powLtBody, testRSBody r, allRSBody]

def wordRS (r N D : ℕ) : ℕ := (N + 1) * D + N + D + r + 1

def tTestRS (r : ℕ) : ℕ := 16 * r + 25

theorem length_program31 (G : RatParams) : (program31 G).length = 74 := rfl

theorem programRS_at (G : RatParams) (r : ℕ) :
    (programRS G r)[Proc.powRS]? = some powLtBody ∧
      (programRS G r)[Proc.testRS]? = some (testRSBody r) := by
  refine ⟨?_, ?_⟩ <;>
  · rw [programRS, List.getElem?_append_right (by norm_num [length_program31]),
      length_program31]
    rfl

theorem testRS_meets {lim : Limits} {P : Program} {d : ℕ} (r : ℕ)
    (hP : P[Proc.testRS]? = some (testRSBody r)) (hpow : P[Proc.powRS]? = some powLtBody)
    (hd : d + 1 ≤ lim.depth) (N D : ℕ) (_hN : 1 ≤ N) (hD : 1 ≤ D)
    (hword : ((wordRS r N D : ℕ) : ℤ) ≤ lim.word) (μ : ℕ → ℤ) :
    Meets lim P Proc.testRS d [N, D] μ (tTestRS r) fun r' μ' =>
      μ' = μ ∧ ((r' = 1 ∧ D ^ r ≤ N) ∨ (r' = 0 ∧ ¬ D ^ r ≤ N)) := by
  refine .of_body hP ?_
  unfold wordRS at hword
  have hcall := powLt_meets (lim := lim) (P := P) (d := d + 1) (μ := μ) (g := D) (e := r)
    (t := N + 1) hpow hD (le_trans (by exact_mod_cast (by omega)) hword)
  push_cast at hword
  have : (0 : ℤ) ≤ ((N : ℤ) + 1) * D := by positivity
  refine Ends.callTo hcall (fun r' μ' ⟨hr', hμ'⟩ => ⟨hμ', ?_⟩) (by light_side) (by omega)
    (by simp [tTestRS]; omega)
  simp only [frame, setLocal, List.getD_cons_zero, hr']
  split_ifs with h
  · exact Or.inl ⟨rfl, by omega⟩
  · exact Or.inr ⟨rfl, by omega⟩

def FitsRS (G : RatParams) (r : ℕ) : Prop :=
  ∀ N D₀ : ℕ, D₀ ^ r ≤ N → G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀)

end ImprovedExponents

/-!
# The time functions of the pruned offline routine

`tPre31P` and `tOffline32P` are upstream's `tPre31` and `tOffline32` (`ThreeSumApsp/Programs/Sec4/
ChoosingParameters/{Parameters,Offline}.lean`) with `tPreCoreP` in place of `tPreCore`: the only
change of the pruned solver's running time is the work of the encoder in the shared stage.  They
are fixed here so that the cost analysis (`ImprovedExponents.Cost8P`) and the routine
(`ImprovedExponents.PrunedProgram.Wrapper`) agree.

Adapted from upstream (Apache-2.0).
-/

namespace Light.Sec4


/-- The time of the pruned preprocessing `pre31P`; c is the constant of the pruned shared stage. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (tPre31)
def tPre31P (c : ℕ) (G : RatParams) (N D₀ : ℕ) : ℕ :=
  tLog4 (logFour D₀) + 30 +
    if logFour D₀ < G.m₀ then 0 else
      tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀))
        + tCopy (D₀ * N) + tFill ((D (logFour D₀) - D₀) * N)
        + tPreCoreP c (parOf G N D₀) (switchOf31 G D₀) + 120

/-- The time of the pruned offline routine `offline32P` on an instance with `w` wanted positions.
-/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (tOffline32)
def tOffline32P (c : ℕ) (G : RatParams) (N D₀ w : ℕ) : ℕ :=
  tPre31P c G N D₀ + w * (tQuery31 G D₀ + 30) + 20


/-!
# Corollary 31 with the pruned encoder: the state of the routines and the query

Upstream's routines with rational parameters (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/
Parameters.lean`) keep, from the free pointer on, a flag, the base address and the data structure
of Theorem 30 for the padded matrices (`Built31`, `Ready31`).  With the pruned encoder the data
structure is `DSReadyP` (the encodings right at the leaves with at most `m` symbols `P₀`):
`Built31P`, `Ready31P`.  The query `query31` is upstream's own procedure and body; it meets the
same specification with `Ready31P` (`query31P_meets`) from `QueryAtSpecP`.  The preprocessing
`pre31P` is upstream's `pre31` with `preCoreP` in place of `preCore` (`pre31PBody`, `PreSpec31P`).

Adapted from upstream (Apache-2.0).
-/


open ThreeSumApsp.Spec ImprovedExponents

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-- The data structure of Theorem 30 with pruned encodings for the padded matrices has been built
in the cells after fr. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (Built31)
abbrev Built31P (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (fr : ℕ) (μ : ℕ → ℤ) : Prop :=
  DSReadyP (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
    (paddedYAt N D₀ fr) (blockAt N D₀ fr) (padInnerCols (D (logFour D₀)) X)
    (padInnerRows (D (logFour D₀)) Y) μ

/-- **The cells from fr on hold what a query needs**, with pruned encodings. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (Ready31)
structure Ready31P (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (μ : ℕ → ℤ) : Prop where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  small : logFour D₀ < G.m₀ → μ fr = 0
  large : G.m₀ ≤ logFour D₀ → μ fr = 1 ∧ μ (fr + 1) = blockAt N D₀ fr ∧ Built31P G X Y fr μ

/-- query31 returns the entry (XY)[I, J], keeps the structure ready, and changes only cells of the
structure behind its first three: upstream's procedure, with pruned encodings. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (QuerySpec31)
def QuerySpec31P (lim : Limits) (P : Program) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ) (I J : Fin N), Input31 lim G X Y aX aY fr U → Ready31P G X Y aX aY fr μ →
    ∀ d, d + 3 ≤ lim.depth → Meets lim P Proc.query31 d [(I : ℕ), (J : ℕ), N, D₀, aX, aY, fr] μ
        (tQuery31 G D₀) fun r μ' =>
      r = (X * Y) I J ∧ Ready31P G X Y aX aY fr μ' ∧
          SameOutside μ μ' (fr + 3) (structEnd G N D₀ fr - (fr + 3))

/-- A query to the data structure of Theorem 30 changes only cells of its block, so that the
structure stays ready. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean
-- (Ready31.of_query)
theorem Ready31P.of_query (h : Ready31P G X Y aX aY fr μ) (bX : aX + N * D₀ ≤ fr)
    (bY : aY + D₀ * N ≤ fr) (hm : G.m₀ ≤ logFour D₀) (hkept : ∀ a < blockAt N D₀ fr, μ' a = μ a)
    (hDS : Built31P G X Y fr μ') : Ready31P G X Y aX aY fr μ' := by
  have := add_three_le_blockAt N D₀ fr
  obtain ⟨hflag, hbase, -⟩ := h.large hm
  exact ⟨h.matX.congr_below hkept (by omega), h.matY.congr_below hkept (by omega),
    fun hm' => absurd hm (by omega),
    fun _ => ⟨(hkept _ (by omega)).trans hflag, (hkept _ (by omega)).trans hbase, hDS⟩⟩

/-- query31 reads the flag and calls the query of Theorem 30 if it is 1 and the inner product
otherwise; it returns the entry (XY)[I, J] and keeps the structure ready. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean
-- (query31_meets)
theorem query31P_meets (G : RatParams) (hP : P[Proc.query31]? = some query31Body)
    (hq : QueryAtSpecP lim P) (hip : IpAtSpec lim P) : QuerySpec31P lim P G := by
  intro N D₀ aX aY fr X Y U μ I J hin hR
  have hlim := hin.lim
  have bX := hin.belowX
  have bY := hin.belowY
  refine fun d hd => ⟨query31Body, hP, ?_⟩
  have := hlim.std.space_le
  have := hlim.std.const_le
  have hU0 := hin.zero_le_U
  have := add_three_le_structEnd G N D₀ fr
  have := hlim.space
  unfold query31Body
  -- if mem[fr] = 1
  refine Ends.iteLast (fun hflag => ?_) (fun hflag => ?_) (hT := by simp [tQuery31])
  · -- the data structure has been built: return queryAt(I, J, mem[fr + 1])
    have hlarge : G.m₀ ≤ logFour D₀ := by
      by_contra hc
      have := hR.small (by omega)
      have : μ fr = 1 := by simpa using hflag
      omega
    obtain ⟨-, hbase, hDS⟩ := hR.large hlarge
    have haddr : ((fr : ℤ) + 1).toNat = fr + 1 := by omega
    refine Ends.callTo
      (hq (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
        (paddedYAt N D₀ fr) (blockAt N D₀ fr) _ _ U μ I J (G.t_le _) (hlim.large hlarge)
        (abs_padInnerCols_le hin.absX hU0) (abs_padInnerRows_le hin.absY hU0) hDS _ (by omega)) ?_
      (by light_side [haddr, hbase])
      (hT := by simp [tQuery31, ite_eq_right (not_lt.mpr hlarge), parOf]; omega)
    rintro r μ' ⟨hr, hDS', hout⟩
    have := G.scratch_in_block N D₀ fr
    have := add_three_le_blockAt N D₀ fr
    have := structEnd_large hlarge N fr
    refine ⟨?_, hR.of_query bX bY hlarge (fun a ha => hout a (by omega)) hDS',
      fun a ha => hout a (by omega)⟩
    -- padding changes no entry of the product
    exact hr.trans (congrFun (congrFun
      (Corollary26.padding (D (logFour D₀)) (le_D_logFour D₀) X Y) I) J)
  · -- m is below the threshold: return the inner product ipAt(I, J, N, D, aX, aY)
    have hsmall : logFour D₀ < G.m₀ := by
      by_contra hc
      exact hflag (by simpa using (hR.large (by omega)).1)
    refine Ends.callTo (hip N D₀ aX aY X Y U μ I J hin.one_le_D hR.matX hR.matY hin.absX hin.absY
      (by omega) (by omega) hlim.ip _ (by omega)) ?_
      (hT := by simp [tQuery31, ite_eq_left hsmall]; omega)
    rintro r μ' ⟨hr, rfl⟩
    exact ⟨hr, hR, .refl⟩

/-! ## The preprocessing: text and interface -/

open Pre31 in
/-- The second part of pre31P: the preprocessing of Theorem 30 with the pruned encoder, the base
address and the flag 1. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (preBuild31)
def preBuild31P : Stmt :=
  .call Proc.preCoreP [v Levels, v Log, v Switch, v Size, v Padded, v PadX, v PadY, v Block] Res ;;
  .store (v Free +' k 1) (v Block) ;;
  .store (v Free) (k 1)

/-- The part of pre31P for m ≥ m₀. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (preLarge31)
def preLarge31P : Stmt := prePad31 ;; preBuild31P

open Pre31 in
/-- pre31P(N, D, aX, aY, fr): m and 4^m; for m < m₀ the flag 0, for m ≥ m₀ preLarge31P. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (pre31Body)
def pre31PBody (G : RatParams) : Stmt :=
  .call Proc.log4 [v Dim, v Free +' k 2] Log ;;
  .ite (v Log <' k G.m₀) (.store (v Free) (k 0)) preLarge31P

/-- pre31P prepares the cells from fr on, about which nothing is assumed, for queries to XY. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Parameters.lean (PreSpec31)
def PreSpec31P (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (U : ℤ)
      (μ : ℕ → ℤ), Input31 lim G X Y aX aY fr U → MatAt μ aX X → MatAt μ aY Y →
    ∀ d, d + (G.L (logFour D₀) + 7) ≤ lim.depth → Meets lim P Proc.pre31P d [N, D₀, aX, aY, fr] μ
        (tPre31P c G N D₀) fun _ μ' =>
      Ready31P G X Y aX aY fr μ' ∧ SameOutside μ μ' fr (structEnd G N D₀ fr - fr)





/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Corollaries 26 and 31 in the light language: the preprocessing, with rational parameters

Proof of Corollary 26: "Setting up. Let m := ⌈log₄ D⌉, and pad the inner dimension to 4^m < 4D with
zero columns of X and zero rows of Y." Proof of Corollary 31: "We repeat the proof of Corollary 26
with L := ⌈cm⌉ and t := ⌈θm⌉". Then the preprocessing of Theorem 30 on the padded matrices; "for
smaller m the corollary again holds trivially".

The routine meets its specification (`pre31_meets`). It computes m and branches. Below the threshold
it writes the flag 0 (`PreInput31.ready_small`). From the threshold on it computes L, t and the
addresses, pads X, and pads Y by a copy and a fill with zeros (`prePad31_ends`,
`matAt_padInnerRows`); then it calls the preprocessing of Theorem 30 and writes the base address and
the flag 1 (`preBuild31_ends`, `PreInput31.ready_large`).
-/





/-! ## What the routine is given, and what it leaves -/

/-- What the preprocessing is given: besides what both routines are given, the matrices X and Y
stand at aX and aY. -/
structure PreInput31 (lim : Limits) (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (U : ℤ) (μ : ℕ → ℤ) : Prop
    extends Input31 lim G X Y aX aY fr U where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y

/-- **Y with zero rows**: a copy of Y followed by zeros is the padded matrix. -/
theorem matAt_padInnerRows {F a : ℕ} (mY : MatAt μ aY Y)
    (hcopy : ∀ i < D₀ * N, μ' (a + i) = μ (aY + i))
    (hzero : ∀ i < (F - D₀) * N, μ' (a + D₀ * N + i) = 0) : MatAt μ' a (padInnerRows F Y) := by
  intro i j
  unfold padInnerRows
  by_cases hi : (i : ℕ) < D₀
  · rw [dif_pos hi, Nat.add_assoc, hcopy _ (Nat.mul_add_lt_mul hi j.isLt), ← Nat.add_assoc]
    exact mY ⟨i, hi⟩ j
  · have hrow : (i : ℕ) * N = D₀ * N + ((i : ℕ) - D₀) * N := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' (not_lt.mp hi)]
    have hidx := Nat.mul_add_lt_mul (by have := i.isLt; omega : (i : ℕ) - D₀ < F - D₀) j.isLt
    rw [dif_neg hi, hrow, ← Nat.add_assoc, Nat.add_assoc (a + D₀ * N), hzero _ hidx]

/-! ## From the threshold on -/

/-- The areas from the free pointer on: fr, fr + 1, fr + 2 | X' | Y' | the block of Theorem 30 from
b0 on. F = 4^m is the padded inner dimension, and R the number of cells in the zero rows of Y'. -/
structure Areas31 (lim : Limits) (N D₀ fr F R : ℕ) : Prop where
  F_eq : F = D (logFour D₀)
  R_eq : R = (F - D₀) * N
  base : blockAt N D₀ fr = fr + 3 + N * F + N * F
  base_lt : blockAt N D₀ fr < lim.space
  D_le : D₀ ≤ F
  rows : D₀ * N + R = N * F
  F_le : F ≤ N * F

theorem PreInput31.areas (h : PreInput31 lim G X Y aX aY fr U μ) (hm : G.m₀ ≤ logFour D₀) :
    Areas31 lim N D₀ fr (D (logFour D₀)) ((D (logFour D₀) - D₀) * N) where
  F_eq := rfl
  R_eq := rfl
  base := rfl
  base_lt := (G.blockAt_lt_blockEnd N D₀ fr).trans_le (structEnd_large hm N fr ▸ h.lim.space)
  D_le := le_D_logFour D₀
  rows := by rw [← Nat.add_mul, Nat.add_sub_cancel' (le_D_logFour D₀), Nat.mul_comm]
  F_le := Nat.le_mul_of_pos_left _ h.one_le_N

/-- The time of prePad31. -/
def tPrePad31 (G : RatParams) (N D₀ : ℕ) : ℕ :=
  tCeilMul G.a (logFour D₀) + tCeilMul G.p (logFour D₀) + tPadX N (D (logFour D₀)) + tCopy (D₀ * N)
    + tFill ((D (logFour D₀) - D₀) * N) + 60

/-- The state after prePad31: the locals hold the parameters and the addresses, the padded matrices
stand at their places, and only cells between fr and b0 have changed. -/
def Padded31 (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (aX aY fr : ℕ) (μ : ℕ → ℤ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [N, D₀, aX, aY, fr, logFour D₀, (D (logFour D₀) : ℕ), (G.L (logFour D₀) : ℕ),
      (G.t (logFour D₀) : ℕ), (paddedXAt fr : ℕ), (paddedYAt N D₀ fr : ℕ), (blockAt N D₀ fr : ℕ), r,
      (N * D (logFour D₀) : ℕ)], μ'⟩ ∧
    MatAt μ' (paddedXAt fr) (padInnerCols (D (logFour D₀)) X) ∧
    MatAt μ' (paddedYAt N D₀ fr) (padInnerRows (D (logFour D₀)) Y) ∧
    SameOutside μ μ' fr (blockAt N D₀ fr - fr)

/-! ## The routine -/






/-!
# Corollary 31 with the pruned encoder: the preprocessing, with rational parameters

Upstream's `pre31` (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean`) computes
`m`, pads the matrices and calls the preprocessing of Theorem 30.  `pre31P` is the same text with
`preCoreP` in place of `preCore`; the proof is upstream's with `PreCoreSpecP` and `Ready31P`
(`pre31P_meets`).  The padding stage `prePad31` is upstream's text and is re-verified here only
because its proof is stated for the record of callees `PreCalls31`, whose field `preCore` is now
`PreCoreSpecP`.

Adapted from upstream (Apache-2.0).
-/




/-- The routines that the pruned preprocessing calls meet their specifications. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (PreCalls31)
structure PreCalls31P (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop where
  log4 : Log4Spec lim P
  levels : CeilMulSpec lim P Proc.levels31 G.a G.b
  switch : CeilMulSpec lim P Proc.switch31 G.p G.q
  padX : PadXSpec lim P
  copy : CopySpec lim P
  fill : FillSpec lim P
  preCore : PreCoreSpecP lim P c

/-- Below the threshold the flag 0 is all that a query needs. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (PreInput31.ready_small)
theorem PreInput31.ready_smallP (h : PreInput31 lim G X Y aX aY fr U μ) (hm : logFour D₀ < G.m₀)
    (hkept : SameOn (· < fr) μ μ') (hflag : μ' fr = 0) : Ready31P G X Y aX aY fr μ' :=
  ⟨h.matX.congr_below hkept h.belowX, h.matY.congr_below hkept h.belowY, fun _ => hflag,
    fun hm' => absurd hm' (by omega)⟩

/-- From the threshold on a query needs the flag 1, the base address, and the data structure of
Theorem 30 for the padded matrices. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (PreInput31.ready_large)
theorem PreInput31.ready_largeP (h : PreInput31 lim G X Y aX aY fr U μ) (hm : G.m₀ ≤ logFour D₀)
    (hkept : SameOn (· < fr) μ μ') (hflag : μ' fr = 1) (hbase : μ' (fr + 1) = blockAt N D₀ fr)
    (hDS : Built31P G X Y fr μ') : Ready31P G X Y aX aY fr μ' :=
  ⟨h.matX.congr_below hkept h.belowX, h.matY.congr_below hkept h.belowY,
    fun hm' => absurd hm (by omega), fun _ => ⟨hflag, hbase, hDS⟩⟩

/-! ## From the threshold on -/

/-- **Setting up**: L, t, the addresses, and the padded matrices. The cell fr + 2 holds 4^m. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (prePad31_ends)
theorem prePad31_endsP {c d : ℕ} (C : PreCalls31P lim P c G)
    (h : PreInput31 lim G X Y aX aY fr U μ)
    (hm : G.m₀ ≤ logFour D₀) (hd : d + (G.L (logFour D₀) + 7) ≤ lim.depth) :
    Ends lim P d prePad31
      ⟨frame [N, D₀, aX, aY, fr, logFour D₀], Function.update μ (fr + 2) ((D (logFour D₀) : ℕ) : ℤ)⟩
      (tPrePad31 G N D₀) (Padded31 G X Y aX aY fr μ) := by
  have A := h.areas hm
  unfold prePad31 tPrePad31 Padded31 paddedXAt paddedYAt
  rw [A.base]
  generalize D (logFour D₀) = F at A ⊢
  generalize (F - D₀) * N = R at A ⊢
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁, μ₁ = Function.update μ (fr + 2) ((F : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hμ₁]
  obtain ⟨-, hR, hb0, hb0lt, hDF, hrows, hFN⟩ := A
  have := h.lim.std.space_le
  have := h.lim.std.const_le
  have := h.one_le_D
  have hbX := h.belowX
  have hbY := h.belowY
  have hRZ : ((F : ℤ) - D₀) * N = R := by rw [hR]; push_cast [Nat.cast_sub hDF]; rfl
  have hread : μ₁ (fr + 2) = F := by rw [hμ₁]; exact Function.update_self ..
  have hout₁ : SameOutside μ μ₁ (fr + 2) 1 := hμ₁ ▸ SameOn.refl.write (by omega) _
  have hkept₁ : ∀ b < fr, μ₁ b = μ b := fun b hb => hout₁ b (.inl (by omega))
  have haddr : ((fr : ℤ) + 2).toNat = fr + 2 := by omega
  -- F := mem[fr + 2]
  light_set F using haddr, hread
  -- L := ⌈a m / b⌉
  light_call (C.levels (logFour D₀) μ₁ h.lim.wordL _ (by omega)) with _ μ₁ ⟨rfl, rfl⟩
  -- t := ⌈p m / q⌉
  light_call (C.switch (logFour D₀) μ₁ h.lim.wordT _ (by omega)) with _ μ₁ ⟨rfl, rfl⟩
  -- aX' := fr + 3 ; NF := N * F ; aY' := aX' + NF ; b0 := aY' + NF
  light_set (fr + 3 : ℕ)
  light_set (N * F : ℕ)
  light_set (fr + 3 + N * F : ℕ)
  light_set (fr + 3 + N * F + N * F : ℕ)
  -- padX(N, D, F, aX, aX')
  light_call (C.padX N D₀ F aX (fr + 3) X μ₁ hDF (by omega)
    (h.matX.congr_below hkept₁ hbX) (by omega) (by omega) _ (by omega)) with - μ₂ ⟨hpadX, hout₂⟩
  -- copy(aY, aY', D N)
  light_call (C.copy aY (fr + 3 + N * F) (D₀ * N) μ₂ (by omega) (by omega) (by omega)
    (.inl (by omega)) _ (by omega)) with - μ₃ ⟨hcopy, hout₃⟩
  -- fill(aY' + D N, (F - D) N, 0)
  light_call (C.fill (fr + 3 + N * F + D₀ * N) R 0 μ₃ (by omega) (by omega) _
    (by omega)) using hRZ with r μ₄ ⟨hfill, hout₄⟩
  refine ⟨r, μ₄, rfl, ?_, ?_, fun b hb => ?_⟩
  · exact hpadX.congr fun b _ hb => by rw [hout₄ b (.inl (by omega)), hout₃ b (.inl (by omega))]
  · refine matAt_padInnerRows (h.matY.congr_below hkept₁ hbY) (fun i hi => ?_) (hR ▸ hfill)
    rw [hout₄ _ (.inl (by omega)), hcopy i hi, hout₂ _ (.inl (by omega))]
  · rw [hout₄ b (by omega), hout₃ b (by omega), hout₂ b (by omega), hout₁ b (by omega)]

/-- **The preprocessing of Theorem 30 with the pruned encoder** on the padded matrices, the base
address and the flag 1. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (preBuild31_ends)
theorem preBuild31P_ends {c d : ℕ} (C : PreCalls31P lim P c G)
    (h : PreInput31 lim G X Y aX aY fr U μ)
    (hm : G.m₀ ≤ logFour D₀) (hd : d + (G.L (logFour D₀) + 7) ≤ lim.depth) {σ : State}
    (hσ : Padded31 G X Y aX aY fr μ σ) :
    Ends lim P d preBuild31P σ (tPreCoreP c (parOf G N D₀) (switchOf31 G D₀) + 60) fun σ' =>
      Ready31P G X Y aX aY fr σ'.mem ∧ SameOutside μ σ'.mem fr (structEnd G N D₀ fr - fr) := by
  obtain ⟨r, μ₄, rfl, mX, mY, hout₄⟩ := hσ
  have := (h.areas hm).base
  have := (h.areas hm).base_lt
  have := h.lim.std.space_le
  have := h.lim.std.const_le
  have := G.blockAt_lt_blockEnd N D₀ fr
  have := add_three_le_structEnd G N D₀ fr
  unfold preBuild31P
  -- preCoreP(L, m, t, N, F, aX', aY', b0)
  light_call (C.preCore (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
      (paddedYAt N D₀ fr)
    (blockAt N D₀ fr) _ _ U μ₄ (G.t_le _) (h.lim.large hm) (abs_padInnerCols_le h.absX h.zero_le_U)
    (abs_padInnerRows_le h.absY h.zero_le_U) mX mY
    (by change fr + 3 + N * D (logFour D₀) ≤ _; omega)
    (by change fr + 3 + N * D (logFour D₀) + D (logFour D₀) * N ≤ _
        rw [Nat.mul_comm (D (logFour D₀)) N]; omega) _
    (by change d + 1 + (G.L (logFour D₀) + 6) ≤ _; omega)) using parOf, switchOf31, Sec2.Par.D
    with - μ₅ ⟨hDS, hout₅⟩
  have hout₅ : SameOutside μ₄ μ₅ (blockAt N D₀ fr) (G.blockEnd N D₀ fr - blockAt N D₀ fr) := hout₅
  -- mem[fr + 1] := b0
  light_store (fr + 1) (blockAt N D₀ fr)
  -- mem[fr] := 1
  light_store fr 1
  -- outside the cells from fr to the end of the block nothing has changed
  have hsame : SameOutside μ μ₅ fr (structEnd G N D₀ fr - fr) := by
    rw [structEnd_large hm]
    exact fun b hb => (hout₅ b (by omega)).trans (hout₄ b (by omega))
  dsimp only
  refine ⟨h.ready_largeP hm (fun b (hb : b < fr) => ?_) (Function.update_self ..) ?_
    (dsReadyP_congr hDS fun a ha => ?_), (hsame.write (by omega) _).write (by omega) _⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hsame b (.inl hb)]
  · rw [Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-! ## The routine -/

/-- pre31P meets its specification if its callees meet theirs. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Preprocessing.lean
-- (pre31_meets)
theorem pre31P_meets {c : ℕ} (G : RatParams) (hP : P[Proc.pre31P]? = some (pre31PBody G))
    (C : PreCalls31P lim P c G) : PreSpec31P lim P c G := by
  intro N D₀ aX aY fr X Y U μ hin mX mY
  have h : PreInput31 lim G X Y aX aY fr U μ := ⟨hin, mX, mY⟩
  have hlim := hin.lim
  refine fun d hd => ⟨pre31PBody G, hP, ?_⟩
  have := hlim.std.space_le
  have := hlim.std.const_le
  have := add_three_le_structEnd G N D₀ fr
  have := hlim.space
  have := hlim.m0word
  have hmword : (logFour D₀ : ℤ) ≤ lim.word := by
    have : logFour D₀ ≤ G.a * logFour D₀ := Nat.le_mul_of_pos_left _ (by have := G.hc; omega)
    exact le_trans (by exact_mod_cast (by omega :
      logFour D₀ ≤ G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q)) hlim.mword
  unfold pre31PBody
  -- m := log4(D, fr + 2), which writes 4^m to the cell fr + 2
  refine Ends.callToThen (C.log4 D₀ (fr + 2) μ (by omega) hlim.pow hmword _ (by omega)) ?_
    (hT := by simp [tPre31P, logFour]; omega)
  rintro _ _ ⟨rfl, rfl⟩
  -- if m < m₀
  refine Ends.iteLast (fun hsmall => ?_) (fun hlarge => ?_)
    (hT := by simp [tPre31P, logFour]; omega)
  · -- mem[fr] := 0
    have hm : logFour D₀ < G.m₀ := by simpa [logFour] using hsmall
    have htop : structEnd G N D₀ fr - fr = 3 := by rw [structEnd_small hm]; omega
    refine Ends.storeTo fr 0 ⟨h.ready_smallP hm (fun b (hb : b < fr) => ?_)
      (Function.update_self ..), ?_⟩ (hT := by simp [tPre31P, logFour]; omega)
    · change Function.update (Function.update μ _ _) fr 0 b = μ b
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rw [htop]
      exact (SameOn.refl.write (by omega) _).write (by omega) _
  · have hm : G.m₀ ≤ logFour D₀ := by simpa [logFour] using hlarge
    -- the padded matrices, then the data structure of Theorem 30
    refine Ends.next (tPrePad31 G N D₀) ((prePad31_endsP C h hm hd).mono le_rfl fun σ hσ =>
      (preBuild31P_ends C h hm hd hσ).mono ?_ fun _ hQ => hQ) ?_
    all_goals
      simp only [tPre31P, tPrePad31, ite_eq_right (not_lt.mpr hm)]
      simp [logFour]
      omega






/-!
# Corollary 32 with the pruned encoder: the offline routine

Upstream's `offline32` (`ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean`) runs the
preprocessing and then asks one query for each wanted position.  `offline32P` is the same text with
`pre31P` in place of `pre31`; its specification `OfflineSpec32P` is upstream's `OfflineSpec32` for
the procedure `Proc.offline32P` with the time `tOffline32P`, and the proof is upstream's with
`PreSpec31P`, `QuerySpec31P` and `Ready31P`.

Adapted from upstream (Apache-2.0).
-/




open Offline32 in
/-- offline32P(N, D, w, U, x, y, wi, wj, out, fr): preprocess with the pruned encoder, then ask one
query for each wanted position and store its answer. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (offline32Body)
def offline32PBody : Stmt :=
  .call Proc.pre31P [v Size, v Dim, v MatX, v MatY, v Free] Res ;;
  .for Pos (v Count) offlineAsk32

/-- What a query needs depends only on the cells of X, of Y, and on the cells from fr on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (ready31_congr)
theorem ready31P_congr (h : Ready31P G X Y aX aY fr μ)
    (hX : ∀ a, aX ≤ a → a < aX + N * D₀ → μ' a = μ a)
    (hY : ∀ a, aY ≤ a → a < aY + D₀ * N → μ' a = μ a) (hfr : ∀ a, fr ≤ a → μ' a = μ a) :
    Ready31P G X Y aX aY fr μ' := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun hs => ?_, fun hl => ?_⟩
  · rw [hX _ (by omega) ?_]
    · exact h.matX i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl D₀)
      have := j.isLt
      omega
  · rw [hY _ (by omega) ?_]
    · exact h.matY i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl N)
      have := j.isLt
      omega
  · rw [hfr _ le_rfl]
    exact h.small hs
  · obtain ⟨h1, h2, h3⟩ := h.large hl
    refine ⟨by rw [hfr _ le_rfl]; exact h1, by rw [hfr _ (by omega)]; exact h2,
      dsReadyP_congr h3 fun a ha => hfr a ?_⟩
    unfold blockAt at ha
    omega

/-- offline32P writes the wanted entries of XY to out. Below fr it changes only the output; nothing
is assumed about the cells from fr on. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean (OfflineSpec32)
def OfflineSpec32P (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY aI aJ out fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (U : ℤ) (u : ℤ) (μ : ℕ → ℤ) (WI WJ : List ℕ),
    Input31 lim G X Y aX aY fr U → OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ →
    ∀ d, d + (G.L (logFour D₀) + 8) ≤ lim.depth → Meets lim P Proc.offline32P d
      [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr] μ (tOffline32P c G N D₀ WI.length)
      fun _ μ' => Seg μ' out ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) ∧
        ∀ a < fr, (a < out ∨ out + WI.length ≤ a) → μ' a = μ a

/-- The specification holds for the program with more procedures appended. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/ChoosingParameters/Offline.lean
-- (OfflineSpec32.append)
theorem OfflineSpec32P.append {c : ℕ} (h : OfflineSpec32P lim P c G) (R : Program) :
    OfflineSpec32P lim (P ++ R) c G :=
  fun N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd =>
    (h N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd).append R

theorem offline32P_meets {c : ℕ} (hP : P[Proc.offline32P]? = some offline32PBody)
    (hpre : PreSpec31P lim P c G) (hq : QuerySpec31P lim P G) : OfflineSpec32P lim P c G := by
  intro N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin
  refine fun d hd => ⟨offline32PBody, hP, ?_⟩
  have := hg.lim.std.space_le
  have := hg.lim.space
  have := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have := hin.out_le
  have hzip : (WI.zip WJ).length = WI.length := by simp [hlen]
  refine Ends.callToThen (hpre N D₀ aX aY fr X Y U μ hg hin.matX hin.matY _ (by omega)) ?_
    (hT := by simp [tOffline32P]; omega)
  rintro r μ₁ ⟨hready, hblock⟩
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩ ∧
      Answered (Ready31P G X Y aX aY fr) (· < fr) out
        ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ i μ')
    WI.length (tQuery31 G D₀ + 20) ?start ?round ?done ?bound
    (hT := by simp [tOffline32P]; ring_nf; omega)
  case start =>
    exact ⟨r, μ₁, by rw [update_frame_setLocal]; rfl, hready, Seg.nil,
      SameOn.mono hblock fun a ha => Or.inl ha.2⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨r, μ', rfl, hinv⟩
    rw [← hzip, ← List.length_map (as := WI.zip WJ) fun q => entryN X Y q.1 q.2] at hinv
    refine ⟨hinv.all, fun a ha hoff => hinv.same a ⟨?_, ha⟩⟩
    simpa [hlen] using hoff
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hinv⟩
    have := hin.rows_le
    have := hin.cols_le
    have hiJ : i < WJ.length := by omega
    have hIN : WI[i] < N := hin.rows_lt _ (List.getElem_mem hi)
    have hJN : WJ[i] < N := hin.cols_lt _ (List.getElem_mem hiJ)
    have hrow : μ' (aI + i) = ((WI[i] : ℕ) : ℤ) :=
      (hinv.read hin.rows (j := i) (by simpa using hi)
        (by rcases hin.out_rows with h | h <;> omega) (by omega)).trans (List.getElem_map _)
    have hcol : μ' (aJ + i) = ((WJ[i] : ℕ) : ℤ) :=
      (hinv.read hin.cols (j := i) (by simpa using hiJ)
        (by rcases hin.out_cols with h | h <;> omega) (by omega)).trans (List.getElem_map _)
    refine Ends.callToThen (hq N D₀ aX aY fr X Y U μ' ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩ hg hinv.ready _
      (by omega)) ?_ (ha := by light_side [hrow, hcol])
    rintro _ μ₂ ⟨rfl, hready, hquery⟩
    light_store (out + i) ((X * Y) ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩)
    have hstep := hinv.step (by simpa [hlen] using hi) hquery (fun j hj => Or.inl (by omega))
      (fun a ha => Or.inl (by omega)) (ready31P_congr hready
        (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matX with h | h <;> omega) _ _)
        (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matY with h | h <;> omega) _ _)
        fun a ha => Function.update_of_ne (by omega) _ _)
    rw [List.getElem_map, List.getElem_zip, entryN, dite_eq_left ⟨hIN, hJN⟩] at hstep
    exact ⟨by simp, _, _, by rw [update_frame_setLocal]; rfl, hstep⟩





/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The preprocessing of Theorem 30, at a given place of the memory

Proof of Theorem 30, "Preprocessing". The routine first runs the stage that it shares with
Theorem 5: the list of the subsets, the tables for the rows and columns, and the encodings of all
row bands and column bands. It notes t in the directory, computes the addresses of the areas of
Section 4 (preCoreAddr), starts the trie area with the array [0], and computes the values of all the
boxes of all tiles, by Lemma 29 (preCoreFinish). There is one lemma for each of the two named parts;
preCore_spec puts them behind the shared stage.
-/




/-! ## The program -/

namespace PreCore

/-- The local variables of preCore: the arguments L, m, t, N, D, aX, aY, b0; a local for results
that are not used; the address of WD, the number nB, the addresses of CUR, BOX, FP, ROOTS, the
number m - t, and the address of TR. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Inner : ℕ := 1
@[inherit_doc Levels] abbrev Switch : ℕ := 2
@[inherit_doc Levels] abbrev Size : ℕ := 3
@[inherit_doc Levels] abbrev Width : ℕ := 4
@[inherit_doc Levels] abbrev MatX : ℕ := 5
@[inherit_doc Levels] abbrev MatY : ℕ := 6
@[inherit_doc Levels] abbrev Base : ℕ := 7
@[inherit_doc Levels] abbrev Void : ℕ := 8
@[inherit_doc Levels] abbrev Digits : ℕ := 9
@[inherit_doc Levels] abbrev Bands : ℕ := 10
@[inherit_doc Levels] abbrev Cur : ℕ := 11
@[inherit_doc Levels] abbrev Box : ℕ := 12
@[inherit_doc Levels] abbrev Free : ℕ := 13
@[inherit_doc Levels] abbrev Roots : ℕ := 14
@[inherit_doc Levels] abbrev Last : ℕ := 15
@[inherit_doc Levels] abbrev Tries : ℕ := 16

end PreCore

open PreCore in
/-- The addresses of the areas of Section 4, which lie one behind the other from WD on. -/
def preCoreAddr : Stmt :=
  .set Digits (M (v Base +' k Dir.sharedEnd)) ;;
  .set Bands (M (v Base +' k Dir.bands)) ;;
  .set Cur (v Digits +' v Levels) ;;
  .set Box (v Cur +' v Levels) ;;
  .set Free (v Box +' v Levels +' v Inner) ;;
  .set Roots (v Free +' k 1) ;;
  .set Last (v Inner -' v Switch) ;;
  .set Tries (v Roots +' v Bands *' v Bands)

open PreCore in
/-- The trie array starts as [0], of length 1; then the tries of all tiles. -/
def preCoreFinish : Stmt :=
  .store (v Tries) (k 0) ;;
  .store (v Free) (k 1) ;;
  .call Proc.allTiles [M (v Base +' k Dir.encA), M (v Base +' k Dir.encB), v Bands,
    M (v Base +' k Dir.leaves), v Roots, v Tries, v Free, v Cur, v Box, v Levels, v Last] Void

/-- What the locals hold after the shared stage; r is its result. -/
def preShared (p : Sec2.Par) (t aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  [p.L, p.m, t, p.N, p.D, aX, aY, b0, r]

/-- What the locals hold after the addresses have been computed. -/
def preLocals (p : Sec2.Par) (t aX aY b0 : ℕ) (r : ℤ) : List ℤ :=
  preShared p t aX aY b0 r ++ [(aWD p b0 : ℤ), p.nB, aCUR p b0, aBOX p b0, aFP p b0, aROOTS p b0,
    (p.m - t : ℕ), aTR p b0]

variable {lim : Limits} {P : Program} {d : ℕ} {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L}
  {aX aY b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {U : ℤ} {μ : ℕ → ℤ}

/-! ## The addresses -/

/-! ## The tries -/

/-- The arguments of the call of allTiles, and the data behind them. -/
def allArgs (p : Sec2.Par) (t : ℕ) (hmL : p.m ≤ p.L) (b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) :
    AllTilesArgs where
  L := p.L
  m := p.m
  t := t
  nB := p.nB
  encA := encRow p hmL X
  encB := encCol p hmL Y
  aENCA := p.aENCA b0
  aENCB := p.aENCB b0
  aR := aROOTS p b0
  tr := aTR p b0
  cap := trieCap p t
  fp := aFP p b0
  cur := aCUR p b0
  box := aBOX p b0

/-- The trie area with the array [0], after the two stores. -/
theorem trieMem_start (p : Sec2.Par) (t b0 : ℕ) (μ : ℕ → ℤ) :
    TrieMem (Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1) (aTR p b0)
      (trieCap p t) (aFP p b0) [0] := by
  obtain ⟨⟩ := areas p t b0
  refine ⟨fun i hi => ?_, Function.update_self .., by simp [trieCap], Or.inl (by omega)⟩
  obtain rfl : i = 0 := by simpa using hi
  rw [Nat.add_zero, Function.update_of_ne (by omega), Function.update_self]
  rfl

/-! ## The routine -/






/-!
# The preprocessing of Theorem 30 with the pruned shared stage

Upstream's `preCoreBody` runs the shared stage `Sec2.pShared`, notes `t` in the directory,
computes the addresses of the areas of Section 4 (`preCoreAddr`) and builds the tries of all
tiles (`preCoreFinish`).  The new procedure `preCoreP` (`preCorePBody`) is the same statement
with the pruned shared stage `Proc.sharedP` in place of `Sec2.pShared`: it leaves the encodings
right at the leaves with at most `m` symbols `P₀` only (`Sec2.SharedReadyP`), which is all that
`allTiles` on pruned encodings assumes (`AllTilesPreP`), and it establishes `DSReadyP` in the
time `tPreCoreP`.  The proofs are upstream's with `SharedReadyP` in place of `SharedReady`:

* `SharedReadyP.dirCells`: the cells of the directory that the routine reads.
* `preCoreAddrP_spec`, `allArgsP_pre`, `preCoreFinishP_spec`, `preCoreP_spec`: the parts of
  the routine and the routine (`preCore_spec`), under `Sec2.SharedSpecP` and `AllTilesSpecP`.
* `preCoreP_of_base58`: for a program `base58 ++ R` that holds `preCorePBody` at `Proc.preCoreP`
  and meets `Sec2.SharedSpecP`, the specification `PreCoreSpecP` holds; the bodies and the
  specifications of upstream's routines 40 to 48 come from `at_base58` and `specs40`.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Directory.lean`, `Areas.lean`,
`Preprocessing.lean`, `Routines.lean` and `Program.lean` (Apache-2.0).
-/




/-! ## The program -/

open PreCore in
/-- preCoreP(L, m, t, N, D, aX, aY, b0) builds the data structure for the matrices at aX and aY in
the block from b0 on, with the pruned shared stage: upstream's `preCoreBody` with `Proc.sharedP`
in place of `Sec2.pShared`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean (preCoreBody)
def preCorePBody : Stmt :=
  .call Proc.sharedP [v Levels, v Inner, v Size, v Width, v MatX, v MatY, v Base] Void ;;
  .store (v Base +' k Dir.switch) (v Switch) ;;
  preCoreAddr ;;
  preCoreFinish

/-! ## The addresses -/

/-- The addresses of the areas of Section 4 are computed as the map says. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean
-- (preCoreAddr_spec)
theorem preCoreAddrP_spec (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U)
    (hSR : Sec2.SharedReadyP p hmL aX aY b0 X Y μ) (r : ℤ) :
    Ends lim P d preCoreAddr ⟨frame (preShared p t aX aY b0 r), μ⟩ 38
      (· = ⟨frame (preLocals p t aX aY b0 r), μ⟩) := by
  have dir := hSR.dirCells
  light_facts hlim hlim.std
  obtain ⟨⟩ := areas p t b0
  unfold preLocals preShared
  -- the product nB², in the integers
  have hsq : ((p.nB * p.nB : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.nB * p.nB ≤ lim.space)
  have htr : ((aROOTS p b0 + p.nB * p.nB : ℕ) : ℤ) = aTR p b0 := by
    exact_mod_cast (by omega : aROOTS p b0 + p.nB * p.nB = aTR p b0)
  have : (0 : ℤ) ≤ (p.nB : ℤ) * p.nB := by positivity
  push_cast at hsq htr
  -- digits := dir[30]; bands := dir[9]
  light_set (aWD p b0 : ℕ) using dir.sharedEnd
  light_set (p.nB : ℕ) using dir.bands
  -- cur := digits + L; box := cur + L; free := box + L + m; roots := free + 1
  light_set (aCUR p b0 : ℕ)
  light_set (aBOX p b0 : ℕ)
  light_set (aFP p b0 : ℕ)
  light_set (aROOTS p b0 : ℕ)
  -- last := m - t; tries := roots + nB nB
  light_set (p.m - t : ℕ)
  light_set (aTR p b0 : ℕ)
  rfl

/-! ## The tries -/

/-- The block, after the pruned shared stage and with the trie array [0], holds what allTiles on
pruned encodings assumes. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean (allArgs_pre)
theorem allArgsP_pre (h : Lim30 lim p t b0 U) (ht : t ≤ p.m) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hSR : Sec2.SharedReadyP p hmL aX aY b0 X Y μ)
    (hTM : TrieMem μ (aTR p b0) (trieCap p t) (aFP p b0) [0]) :
    AllTilesPreP lim μ (allArgs p t hmL b0 X Y) := by
  -- a negative bound U is possible only if there are no entries; then 0 is a bound as well
  obtain ⟨U', hU0, hX', hY', hvalue⟩ : ∃ U' : ℤ, 0 ≤ U' ∧ (∀ i j, |X i j| ≤ U') ∧
      (∀ i j, |Y i j| ≤ U') ∧ 10 ^ p.m * ((7 ^ p.L * U') * (7 ^ p.L * U')) ≤ lim.word := by
    rcases le_or_gt 0 U with h0 | h0
    · exact ⟨U, h0, hX, hY, h.value⟩
    · have hword : (0 : ℤ) ≤ lim.word := le_trans (by norm_num) h.std.const_le
      exact ⟨0, le_rfl, fun i j => absurd ((abs_nonneg _).trans (hX i j)) (not_le.mpr h0),
        fun i j => absurd ((abs_nonneg _).trans (hY i j)) (not_le.mpr h0), by simpa using hword⟩
  have := h.space
  have hT : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  exact
    { std := h.std
      t_le := ht
      m_le := hmL
      value_le := ⟨7 ^ p.L * U', 7 ^ p.L * U',
        fun β τ => (abs_enc_le hmL X Y U' hU0 hX' hY' β β).1 τ,
        fun β τ => (abs_enc_le hmL X Y U' hU0 hX' hY' β β).2 τ, hvalue⟩
      pow_le := h.pow_le
      cap_ge := le_rfl
      order := by simp only [allArgs]; rw [hT]; omega
      segA := fun β hβ => hSR.encA β hβ
      segB := fun β hβ => hSR.encB β hβ
      trie := hTM }

/-- After the pruned shared stage, the last part completes the data structure; it changes only
cells from CUR to the end of the block. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean
-- (preCoreFinish_spec)
theorem preCoreFinishP_spec (hAll : AllTilesSpecP lim P) (hlim : Lim30 lim p t b0 U)
    (ht : t ≤ p.m) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U) (hd : d + 5 ≤ lim.depth)
    (r : ℤ) (hSR : Sec2.SharedReadyP p hmL aX aY b0 X Y μ) (hcellT : μ (b0 + 31) = t) :
    Ends lim P d preCoreFinish ⟨frame (preLocals p t aX aY b0 r), μ⟩
      (tAllTiles p.L p.m t p.nB + 28) fun σ' =>
      DSReadyP p t hmL aX aY b0 X Y σ'.mem ∧
        SameOutside μ σ'.mem (aCUR p b0) (top p t b0 - aCUR p b0) := by
  light_facts hlim hlim.std
  have : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold preLocals preShared
  -- TR[0] := 0; FP := 1
  light_store (aTR p b0) 0
  light_store (aFP p b0) 1
  have hTM := trieMem_start p t b0 μ
  have same : SameOutside μ (Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1)
      (aCUR p b0) (top p t b0 - aCUR p b0) :=
    (SameOutside.refl.update (by omega) 0).update (by omega) 1
  generalize Function.update (Function.update μ (aTR p b0) 0) (aFP p b0) 1 = μ₁ at *
  have hSR₁ : Sec2.SharedReadyP p hmL aX aY b0 X Y μ₁ :=
    hSR.of_agree fun b hb _ => same b (Or.inl (by omega))
  have dir := hSR₁.dirCells
  -- the tries of all tiles
  light_call (hAll _ μ₁ (allArgsP_pre hlim ht hX hY hSR₁ hTM))
    using allArgs, dir.encA, dir.encB, dir.leaves, Sec2.Par.T with r' μ₂ ⟨hTM₂, hroots, same₂⟩
  have : SameOutside μ μ₂ (aCUR p b0) (top p t b0 - aCUR p b0) :=
    same.then same₂ fun b hb =>
      ⟨hb, by change b < aCUR p b0 ∨ aTR p b0 + trieCap p t ≤ b; omega⟩
  exact ⟨⟨hSR.of_agree fun b hb _ => this b (Or.inl (by omega)),
    (this _ (Or.inl (by omega))).trans hcellT, hroots, hTM₂.seg⟩, this⟩

/-! ## The routine -/

/-- **preCoreP** meets its specification: the pruned shared stage, then upstream's own parts. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Preprocessing.lean (preCore_spec)
theorem preCoreP_spec {c : ℕ} (hP : P[Proc.preCoreP]? = some preCorePBody)
    (hShared : Sec2.SharedSpecP lim P c) (hAll : AllTilesSpecP lim P) :
    PreCoreSpecP lim P c := by
  intro p t hmL aX aY b0 X Y U μ ht hlim hX hY hMX hMY haX haY
  refine fun d hd => ⟨preCorePBody, hP, ?_⟩
  light_facts hlim hlim.std
  have : p.sharedEnd b0 = aWD p b0 := rfl
  obtain ⟨⟩ := areas p t b0
  unfold tPreCoreP
  -- the pruned shared stage
  light_call (hShared p hmL aX aY b0 μ X Y U
    { space := by omega, matX := hMX, matY := hMY, belowX := haX, belowY := haY, absX := hX
      absY := hY, seven := hlim.enc, ten := hlim.pow }) with r μ₁ ⟨hSR₁, same₁⟩
  -- dir[31] := t
  light_store (b0 + 31) t
  have hSR₂ : Sec2.SharedReadyP p hmL aX aY b0 X Y (Function.update μ₁ (b0 + 31) t) :=
    hSR₁.of_agree fun b _ hb => Function.update_of_ne hb ..
  -- the addresses
  light_piece (preCoreAddrP_spec ht hlim hSR₂ r) with _ rfl
  -- the tries
  refine (preCoreFinishP_spec hAll hlim ht hX hY (by omega) r hSR₂
    (Function.update_self ..)).mono (by simp; omega) ?_
  rintro σ' ⟨hDS, same₂⟩
  refine ⟨hDS, fun b hb => ?_⟩
  rw [same₂ b (by omega), Function.update_of_ne (by omega), same₁ b (by omega)]

/-! ## In a program that begins with `base58` -/

/-- **The preprocessing with the pruned shared stage**, in every program that begins with
upstream's `base58`, holds `preCorePBody` at `Proc.preCoreP` and meets the specification of the
pruned shared stage.  The routines 40 to 48 are upstream's (`specs40`), and so are the bodies of
`fillList`, `tile` and `allTiles`, which are re-verified on pruned encodings. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Routines.lean (preCoreSpec_of,
-- preCoreSpec_all) and Program.lean (preCore_base58)
theorem preCoreP_of_base58 {P R : Program} {c : ℕ} (hP : P = base58 ++ R)
    (hpre : P[Proc.preCoreP]? = some preCorePBody) (hsh : Sec2.SharedSpecP lim P c) :
    PreCoreSpecP lim P c := by
  intro p t hmL aX aY b0 X Y U μ ht hlim
  have h40 : Has40 P := hP ▸ has40_base58 R
  have S := specs40 h40 hlim.std
  have hFill : FillListSpecP lim P :=
    fillListP_meets (h40 9 (by omega)) S.nineFirst S.nineNext S.starFirst S.horner S.insert
      S.sumTen
  have hTile : TileSpecP lim P := tileP_spec (h40 10 (by omega)) S.newRoot hFill
  have hAll : AllTilesSpecP lim P := allTilesP_spec (h40 11 (by omega)) hTile
  exact preCoreP_spec hpre hsh hAll p t hmL aX aY b0 X Y U μ ht hlim






/-!
# A query, from the block that holds the data structure on pruned encodings

Upstream's `queryAt_spec` proves the routine `queryAtBody` (procedure 55: the sizes and the bands
from the directory, the areas, the digits of the output string by `outDigits`, the sum of Lemma 28
by `queryCore`) under `DSReady`, which holds the encodings of all bands as full segments.  Of the
data structure, the routine reads the directory, the tables, the roots, the tries and — in
`queryCore` only — the cells of the leaves of order below `t` contributing to the output string of
the position, which have at most `m` symbols `P₀`.  So the routine is correct under `DSReadyP`,
where the encodings are right at these leaves only: `queryAtP_spec` is `queryAt_spec` with
`DSReadyP` in the pre- and postcondition and `QueryCoreSpecP` (`queryCoreP_spec`) in place of
`QueryCoreSpec`; the body and the time are upstream's.  The parts of the proof that do not read
the data structure (`queryAtAreas_spec`, `coreArgs`, `coreArgs_value`, …) are reused; those that
do are copied with `DSReadyP` in place of `DSReady`, under the same names with a `P`.

`queryAtP_of_base58` discharges the assumptions for every program `base58 ++ R` that begins with
upstream's 58 procedures, as upstream's `queryAt_base58`.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean`, `Directory.lean`,
`Areas.lean`, `Routines.lean` and `Program.lean` (Apache-2.0).
-/




section Proof


/-! ## The first part -/

/-- The first part reads the sizes, the addresses of the tables, and the two bands. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAtReads_spec)
theorem queryAtReadsP_spec (hlim : Lim30 lim p t b0 U) (hds : DSReadyP p t hmL aX aY b0 X Y μ)
    {I J : ℕ} (hI : I < p.N) (hJ : J < p.N) :
    Ends lim P d queryAtReads ⟨frame [(I : ℤ), (J : ℤ), (b0 : ℤ)], μ⟩ 90
      (· = ⟨frame (queryAtRead p t b0 I J), μ⟩) := by
  have := hlim.std.space_le
  have : b0 + 31 < lim.space ∧ p.aBAND b0 + p.N ≤ lim.space := by
    have := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have dir := hds.shared.dirCells
  have cellT : μ ((b0 : ℤ) + 31).toNat = (t : ℕ) :=
    (congrArg μ (toNat_natCast_add_natCast b0 31)).trans hds.cellT
  have bandI := hds.shared.band I hI
  have bandJ := hds.shared.band J hJ
  -- levels := dir[0]; inner := dir[1]; switch := dir[31]; outer := dir[4]
  light_set (p.L : ℕ) using dir.levels
  light_set (p.m : ℕ) using dir.inner
  light_set (t : ℕ) using cellT
  light_set (p.Lo : ℕ) using dir.outer
  -- blocks := dir[7]; bands := dir[9]; leaves := dir[10]
  light_set (p.K0 : ℕ) using dir.blocks
  light_set (p.nB : ℕ) using dir.bands
  light_set (p.T : ℕ) using dir.leaves
  -- bandTab := dir[22]; blockTab := dir[23]; digitTab := dir[24]; digits := dir[30]
  light_set (p.aBAND b0 : ℕ) using dir.band
  light_set (p.aBLOCK b0 : ℕ) using dir.block
  light_set (p.aDIG3 b0 : ℕ) using dir.digits
  light_set (aWD p b0 : ℕ) using dir.sharedEnd
  -- bandI := bandTab[I]; bandJ := bandTab[J]
  light_set (I / (p.K0 * p.N0) : ℕ) using bandI
  light_set (J / (p.K0 * p.N0) : ℕ) using bandJ
  rfl

/-! ## The call of outDigits -/

/-- The block holds what outDigits assumes. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (outArgs_pre)
theorem outArgsP_pre (hlim : Lim30 lim p t b0 U) (hds : DSReadyP p t hmL aX aY b0 X Y μ)
    {I J : ℕ} (hI : I < p.N) (hJ : J < p.N) : OutDigitsPre lim μ (outArgs p b0 I J) := by
  have hgI : I / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hgJ : J / p.N0 % p.K0 < p.K0 := Nat.mod_lt _ (K0_pos hmL)
  have hidx : I / p.N0 % p.K0 * p.K0 + J / p.N0 % p.K0 < p.KK := Nat.mul_add_lt_mul hgI hgJ
  -- the three tables lie below WD, and WD inside the memory
  have := hlim.space
  have := Nat.mul_add_le_mul hidx (le_refl p.L)
  have := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have : p.L - p.m = p.Lo := rfl
  obtain ⟨⟩ := areas p t b0
  refine
    { std := hlim.std
      m_le := hmL
      gI_lt := hgI
      gJ_lt := hgJ
      index_lt := tableIndex_lt p.L p.m (⟨_, hgI⟩, ⟨_, hgJ⟩)
      segMask := segN_of_segB (hds.shared.mask _ hidx)
      segI := hds.shared.dig3 I hI
      segJ := hds.shared.dig3 J hJ
      lenI := length_digitList ..
      lenJ := length_digitList ..
      ltI := fun _ => lt_of_mem_digitList (by norm_num)
      ltJ := fun _ => lt_of_mem_digitList (by norm_num)
      spaceMasks := by change p.aMASK b0 + p.KK * p.L < lim.space; omega
      apartMask := ?_
      apartI := ?_
      apartJ := ?_
      spaceI := ?_
      spaceJ := ?_
      spaceDest := ?_ }
  -- the six fields that are left: the tables lie apart from WD, and all within the memory
  all_goals
    simp only [outArgs, OutDigitsArgs.base]
    omega

/-- The third part writes the digits of the output string of (I, J) at WD. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAtOut_spec)
theorem queryAtOutP_spec (hOut : OutDigitsSpec lim P) (hlim : Lim30 lim p t b0 U)
    (hds : DSReadyP p t hmL aX aY b0 X Y μ) {I J : ℕ} (hI : I < p.N) (hJ : J < p.N)
    (hd : d + 1 ≤ lim.depth) :
    Ends lim P d queryAtOut ⟨frame (queryAtLocals p t b0 I J), μ⟩ (tOutDigits p.L + 40) fun σ' =>
      ∃ (r : ℤ) (μ' : ℕ → ℤ), σ' = ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ'⟩ ∧
        SegN μ' (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J)) ∧
        SameOutside μ μ' (aWD p b0) p.L := by
  have := hlim.std.space_le
  have hpre := outArgsP_pre hlim hds hI hJ
  have blockI := hds.shared.block I hI
  have blockJ := hds.shared.block J hJ
  have := hlim.space
  have := Nat.mul_add_le_mul hI (le_refl p.Lo)
  have := Nat.mul_add_le_mul hJ (le_refl p.Lo)
  have : b0 + 31 < lim.space ∧ p.aBLOCK b0 + p.N ≤ lim.space ∧
      p.aDIG3 b0 + p.N * p.Lo ≤ lim.space := by
    obtain ⟨⟩ := areas p t b0
    omega
  have hprodI : ((p.aDIG3 b0 + I * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.aDIG3 b0 + I * p.Lo ≤ lim.space)
  have hprodJ : ((p.aDIG3 b0 + J * p.Lo : ℕ) : ℤ) ≤ lim.space := by
    exact_mod_cast (by omega : p.aDIG3 b0 + J * p.Lo ≤ lim.space)
  have : (0 : ℤ) ≤ (I : ℤ) * p.Lo := by positivity
  have : (0 : ℤ) ≤ (J : ℤ) * p.Lo := by positivity
  push_cast at hprodI hprodJ
  -- outDigits(blockTab[I], blockTab[J], digitTab + I (L - m), digitTab + J (L - m), dir[21], …)
  light_call (hOut _ μ hpre) using queryAtLocals, queryAtRead, outArgs, blockI, blockJ,
    hds.shared.dirCells.mask with r μ' h
  refine ⟨r, μ', rfl, ?_, h.2⟩
  rw [digitsO_outStrOfPos]
  exact h.1

/-! ## The call of queryCore -/

/-- The block, with the digits of the output string at WD, holds what queryCore assumes of pruned
encodings: the encodings of the two bands are right at the leaves with at most m symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (coreArgs_pre)
theorem coreArgsP_pre (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U) (hX : ∀ i j, |X i j| ≤ U)
    (hY : ∀ i j, |Y i j| ≤ U) (hds : DSReadyP p t hmL aX aY b0 X Y μ) (I J : Fin p.N)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    QueryCorePreP lim μ (coreArgs p t hmL b0 X Y I J) := by
  have hU : 0 ≤ U := (abs_nonneg _).trans (hX I ⟨0, Nat.pow_pos (by norm_num)⟩)
  have hβ : (I : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N I I.isLt
  have hβ' : (J : ℕ) / (p.K0 * p.N0) < p.nB := bandOf_lt_numBands hmL p.N J J.isLt
  -- the encodings lie below WD, the tries behind the scratch strings
  have := hlim.space
  have := length_dsTries_le p t hmL X Y
  have := Nat.mul_add_le_mul hβ (le_refl p.T)
  have := Nat.mul_add_le_mul hβ' (le_refl p.T)
  have : 10 ^ p.L = p.T := rfl
  obtain ⟨⟩ := areas p t b0
  refine
    { std := hlim.std
      t_le := ht
      card := card_innerSetO_outStrOfPos (stdLayout hmL) I J
      segA := hds.shared.encA _ hβ
      segB := hds.shared.encB _ hβ'
      segT := hds.trie
      segDigits := hwd
      walk := coreArgs_walk I J ht
      sums := coreArgs_sums I J ht hlim hU hX hY
      prod := abs_enc_mul_le hlim hU hX hY _ _
      pow := hlim.pow_le
      ss_wd := ?_
      box_wd := ?_
      ss_box := ?_
      ss_aA := ?_
      ss_aB := ?_
      box_aA := ?_
      box_aB := ?_
      ss_tr := ?_
      box_tr := ?_
      aA_lt := ?_
      aB_lt := ?_
      tr_lt := ?_
      wd_lt := ?_
      ss_lt := ?_
      box_lt := ?_ }
  -- the fifteen fields that are left: the areas lie apart from each other and within the memory
  all_goals
    simp only [coreArgs]
    omega

/-- The fourth part returns (XY)[I, J] and changes the scratch strings BOX and SS only. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAtCore_spec)
theorem queryAtCoreP_spec (hCore : QueryCoreSpecP lim P) (ht : t ≤ p.m)
    (hlim : Lim30 lim p t b0 U) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U)
    (hds : DSReadyP p t hmL aX aY b0 X Y μ) (I J : Fin p.N) (hd : d + 2 ≤ lim.depth) (r : ℤ)
    (hwd : SegN μ (aWD p b0) (digitsO (outStrOfPos (stdLayout hmL) I J))) :
    Ends lim P d queryAtCore ⟨frame (queryAtLocals p t b0 I J ++ [r]), μ⟩
      (tQueryCore p.L p.m t + 60) fun σ' =>
        σ'.loc 0 = (X * Y) I J ∧ SameOutside2 μ σ'.mem (aSS p b0) p.m (aBOX p b0) p.L := by
  have := hlim.std.space_le
  have hpre := coreArgsP_pre ht hlim hX hY hds I J hwd
  have hvalue := coreArgs_value (hmL := hmL) (b0 := b0) (X := X) (Y := Y) I J ht
  have dir := hds.shared.dirCells
  have htile := tileOf_lt I J hmL
  have cellRoot : μ (aROOTS p b0 + tileOf p I J)
      = ((dsTries p t hmL X Y).root (tileOf p I J) : ℕ) :=
    hds.roots.read (by rw [length_dsTries_roots]; exact htile)
  have : b0 + 31 < lim.space ∧ aROOTS p b0 + p.nB * p.nB < lim.space := by
    have := hlim.space
    obtain ⟨⟩ := areas p t b0
    omega
  have hmeets := (hCore _ μ hpre _ (by omega))
  have hencA := hpre.aA_lt
  have hencB := hpre.aB_lt
  simp only [coreArgs, tileOf] at hmeets hvalue hencA hencB htile cellRoot
  unfold queryAtLocals queryAtRead
  -- the bands, the root and 10^L become variables; the products in the arguments, in the integers
  generalize 10 ^ p.L = leaves at hencA hencB
  generalize (I : ℕ) / (p.K0 * p.N0) = β at *
  generalize (J : ℕ) / (p.K0 * p.N0) = β' at *
  generalize (dsTries p t hmL X Y).root (β * p.nB + β') = root at *
  have : ((p.aENCA b0 + β * p.T : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
  have : ((p.aENCB b0 + β' * p.T : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (by omega)
  have : ((aROOTS p b0 + (β * p.nB + β') : ℕ) : ℤ) < lim.space := by
    exact_mod_cast (by omega)
  have hroot' : (0 : ℤ) ≤ (β : ℤ) * p.T := by positivity
  have hencB' : (0 : ℤ) ≤ (β' : ℤ) * p.T := by positivity
  have hencA' : (0 : ℤ) ≤ (β : ℤ) * p.nB := by positivity
  have haddr : ((aROOTS p b0 : ℤ) + ((β : ℤ) * p.nB + β')).toNat
      = aROOTS p b0 + (β * p.nB + β') := by exact_mod_cast Int.toNat_natCast _
  push_cast at hencA' hencB' hroot'
  -- queryCore(dir[26] + bandI 10^L, dir[27] + bandJ 10^L, tries, roots[bandI nB + bandJ], …)
  light_call hmeets using dir.encA, dir.encB, haddr, cellRoot with r' μ' h
  refine ⟨?_, h.2⟩
  simp only [setLocal, List.cons_append, frame, List.getD_cons_zero]
  rw [h.1, hvalue]

/-! ## The routine -/

/-- **queryAt** meets its specification on pruned encodings: upstream's routine, under the
assumption that the encodings of the bands are right at the leaves with at most `m` symbols `P₀`
only. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Query.lean (queryAt_spec)
theorem queryAtP_spec (hP : P[Proc.queryAt]? = some queryAtBody) (hOut : OutDigitsSpec lim P)
    (hCore : QueryCoreSpecP lim P) : QueryAtSpecP lim P := by
  intro p t hmL aX aY b0 X Y U μ I J ht hlim hX hY hds
  refine fun d hd => ⟨queryAtBody, hP, ?_⟩
  unfold tQueryAt
  -- the sizes, the tables, the bands
  light_piece (queryAtReadsP_spec hlim hds I.isLt J.isLt) with _ rfl
  -- the areas
  light_piece (queryAtAreas_spec hlim I J) with _ rfl
  -- the digits of the output string, which change WD only
  light_piece (queryAtOutP_spec hOut hlim hds I.isLt J.isLt (by omega))
    with _ ⟨r, μ₁, rfl, hwd, same₁⟩
  have same₁' : SameOutside μ μ₁ (aWD p b0) (3 * p.L + p.m) := same₁.mono le_rfl (by omega)
  -- the sum of Lemma 28, which changes BOX and SS only
  light_piece (queryAtCoreP_spec hCore ht hlim hX hY (hds.of_same same₁') I J (by omega) r hwd)
    with ⟨loc₂, μ₂⟩ ⟨hr, same₂⟩
  have : SameOutside μ μ₂ (aWD p b0) (3 * p.L + p.m) := by
    obtain ⟨⟩ := areas p t b0
    exact same₁'.then same₂ fun b hb => ⟨hb, by omega, by omega⟩
  exact ⟨hr, hds.of_same this, this⟩

end Proof

/-! ## The routine in a program that holds the routines of Section 4 -/

/-- `queryCore` on pruned encodings, in every program that holds the routines of Section 4 at
their numbers. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Routines.lean (specs40)
theorem queryCoreSpecP_of {lim : Limits} {P : Program} (h : Has40 P) (hs : Std lim) :
    QueryCoreSpecP lim P :=
  have S := specs40 h hs
  queryCoreP_spec (h 13 (by omega)) ⟨S.nineFirst, S.nineNext, S.scatter, S.horner, S.lookup⟩

/-- A query at a given place of the memory on pruned encodings, for all limits. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Routines.lean (queryAtSpec_all)
theorem queryAtSpecP_all {P : Program} (h : Has40 P)
    (h55 : P[Proc.queryAt]? = some queryAtBody) : ∀ lim, QueryAtSpecP lim P :=
  fun _ p t hmL aX aY b0 X Y U μ I J ht hlim =>
    queryAtP_spec h55 (specs40 h hlim.std).outDigits (queryCoreSpecP_of h hlim.std)
      p t hmL aX aY b0 X Y U μ I J ht hlim

/-- **A query at a given place of the memory on pruned encodings**, in every program that begins
with upstream's 58 procedures. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/Program.lean (queryAt_base58)
theorem queryAtP_of_base58 {lim : Limits} {P R : Program} (hP : P = base58 ++ R) :
    QueryAtSpecP lim P := by
  subst hP
  exact queryAtSpecP_all (has40_base58 R) (at_base58 rfl R) lim

end Light.Sec4




namespace ImprovedExponents

open ThreeSumApsp.Spec Light Light.Sec3 Light.Sec4

def procsP (G : RatParams) : List Stmt :=
  [Sec2.encodePBody Sec2.pEncStep Proc.encodeP, Sec2.encodeBandsPBody, Sec2.sharedPBody,
    preCorePBody, pre31PBody G, offline32PBody, allBody Proc.testRS Proc.offline32P]

def programP (G : RatParams) (r : ℕ) : Program := programRS G r ++ procsP G

theorem length_programRS (G : RatParams) (r : ℕ) : (programRS G r).length = 77 := rfl

theorem programP_at (G : RatParams) (r n : ℕ) {body : Stmt} (hn : 77 ≤ n := by norm_num)
    (h : (procsP G)[n - 77]? = some body := by rfl) : (programP G r)[n]? = some body := by
  rw [programP, List.getElem?_append_right (by rw [length_programRS]; exact hn),
    length_programRS]
  exact h

theorem programP_at_low (G : RatParams) (r : ℕ) {n : ℕ} {body : Stmt}
    (h : (program31 G)[n]? = some body) : (programP G r)[n]? = some body := by
  rw [programP, programRS, List.append_assoc]
  exact getElem?_append_of_eq_some h _

theorem programP_eq_base58 (G : RatParams) (r : ℕ) :
    programP G r = base58 ++
      (procs31 G ++ [powLtBody, testRSBody r, allRSBody] ++ procsP G) := by
  simp only [programP, programRS, program31, List.append_assoc]

theorem programP_eq_program5 (G : RatParams) (r : ℕ) :
    programP G r = Sec2.program5 ++
      ([.skip, Sec2.thinBruteBody, .skip] ++ List.replicate 11 .skip ++ procs40
        ++ [.skip, queryAtBody, .skip, .skip] ++ procs31 G
        ++ [powLtBody, testRSBody r, allRSBody] ++ procsP G) := by
  simp only [programP, programRS, program31, base58, Sec2.programThin, List.append_assoc]

theorem offline32P_programP (G : RatParams) (r : ℕ) (lim : Limits) :
    OfflineSpec32P lim (programP G r) cShared30 G := by
  refine offline32P_meets (programP_at G r Proc.offline32P)
    (fun N D₀ aX aY fr X Y U μ hin => ?_)
    (fun N D₀ aX aY fr X Y U μ I J hin => ?_)
  · have std := hin.lim.std
    have hcopy : CopySpec lim (programP G r) :=
      copy_ok (programP_at_low G r (program31_at G Proc.copy)) std
    have hfill : FillSpec lim (programP G r) :=
      fill_ok (programP_at_low G r (program31_at G Proc.fill)) std
    have hpreCore : PreCoreSpecP lim (programP G r) cShared30 := by
      intro p t hmL aX' aY' b0 X' Y' U' μ' ht hlim
      have e := programP_eq_program5 G r
      have hsh : Sec2.SharedSpecP lim (programP G r) cShared30 := by
        refine Sec2.sharedP_entry hlim.std (programP_at G r Proc.sharedP)
          (programP_at G r Proc.encodeBandsP) ?_ ?_ (programP_at G r Proc.encodeP)
          (c := Sec2.cShared5) ?_ (by norm_num [Sec2.cShared5, Sec2.cBandArray, Sec2.cEncP]) le_rfl
        · rw [e]; exact Sec2.at_prefix rfl _
        · rw [e]; exact Sec2.at_prefix rfl _
        · rw [e]; exact Sec2.sharedCallees_of_prefix _ lim hlim.std
      exact preCoreP_of_base58 (programP_eq_base58 G r) (programP_at G r Proc.preCoreP)
        hsh p t hmL aX' aY' b0 X' Y' U' μ' ht hlim
    exact pre31P_meets G (programP_at G r Proc.pre31P)
      ⟨log4_meets (programP_at_low G r (program31_at G Proc.log4)) std,
        ceilMul_meets G.hb (programP_at_low G r (program31_at G Proc.levels31)),
        ceilMul_meets G.hq (programP_at_low G r (program31_at G Proc.switch31)),
        padX_meets (programP_at_low G r (program31_at G Proc.padX)) hcopy hfill std,
        hcopy, hfill, hpreCore⟩ N D₀ aX aY fr X Y U μ hin
  · exact query31P_meets G (programP_at_low G r (program31_at G Proc.query31))
      (queryAtP_of_base58 (programP_eq_base58 G r))
      (ipAt_meets (programP_at_low G r (program31_at G Proc.ipAt)) hin.lim.std)
      N D₀ aX aY fr X Y U μ I J hin

theorem offline32P_meets_thinTask {lim : Limits} {P : Program} {G : RatParams} {c d : ℕ}
    (task : OfflineSpec32P lim P c G) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hfit : G.m₀ ≤ logFour x.D → Hyp30 (parOf G x.N x.D) (switchOf31 G x.D))
    (ok : (offline32Need G x.N x.D x.U).Ok lim fr d) :
    Meets lim P Proc.offline32P (d + 1) [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ
      (tOffline32P c G x.N x.D x.w) fun r μ' => thinTask.Post x μ fr r μ' := by
  have hU0 : (0 : ℤ) ≤ (x.U : ℤ) := by positivity
  have : d + (G.a * (4 * x.D) + 12) ≤ lim.depth := ok.depth
  have hm4 := logFour_le_four_mul hpre.D_pos
  have : G.L (logFour x.D) ≤ G.a * (4 * x.D) :=
    (ratParams_L_le_mul G _).trans (Nat.mul_le_mul_left _ hm4)
  have spec := task x.N x.D x.x x.y x.wi x.wj x.out fr (thinMX x) (thinMY x) (x.U : ℤ) (x.U : ℤ) μ
    x.WI x.WJ
    { one_le_D := hpre.D_pos, one_le_N := hpre.N_pos
      lim := lim31_of_need hpre.D_pos hfit ok
      absX := fun i j => hpre.leX.abs_getD_le hU0 _
      absY := fun i j => hpre.leY.abs_getD_le hU0 _
      belowX := hpre.belowX, belowY := hpre.belowY }
    { matX := matAt_thinMX hpre, matY := matAt_thinMY hpre
      rows := hpre.segWI, cols := hpre.segWJ
      length_eq := by rw [hpre.lenWI, hpre.lenWJ]
      rows_lt := hpre.ltWI, cols_lt := hpre.ltWJ
      rows_le := by rw [hpre.lenWI]; exact hpre.belowWI
      cols_le := by rw [hpre.lenWI]; exact hpre.belowWJ
      out_le := by rw [hpre.lenWI]; exact hpre.belowOut
      out_matX := by rw [hpre.lenWI]; exact hpre.apartX
      out_matY := by rw [hpre.lenWI]; exact hpre.apartY
      out_rows := by rw [hpre.lenWI]; exact hpre.apartWI
      out_cols := by rw [hpre.lenWI]; exact hpre.apartWJ }
  rw [hpre.lenWI, map_entryN_thin hpre] at spec
  exact (spec _ (by omega)).mono le_rfl fun r μ' h => ⟨h.1, fun a ha => h.2 a ha.1 ha.2⟩

open Classical in
noncomputable def allInstancesTimeP (G : RatParams) (r : ℕ) : List ℕ → ℕ
  | [N, D, w, _] =>
    tTestRS r + 64 + (if D ^ r ≤ N then tOffline32P cShared30 G N D w
      else 40 * ((w + 1) * (D + 1)))
  | _ => 0

def allInstancesNeedP (G : RatParams) (r : ℕ) : List ℕ → Need
  | [N, D, _, U] =>
    ⟨wordRS r N D + (100 + D * (U * U)) + (offline32Need G N D U).word,
      N + 1 + (offline32Need G N D U).cells, 2 + (offline32Need G N D U).depth⟩
  | _ => ⟨0, 0, 0⟩

theorem allInstancesNeedP_poly (G : RatParams) (r : ℕ) : PolyNeedN (allInstancesNeedP G r) := by
  set κ : ℕ := 1405 + r + 4 * G.a + 4 * G.p + G.b + G.q + G.m₀ + 14 with hκdef
  refine ⟨κ, 20, fun ps => ?_⟩
  match ps with
  | [N, D, w, U] =>
    rw [show polyBound κ 20 [N, D, w, U] =
      2 ^ κ * ((N + 1) * ((D + 1) * ((w + 1) * (U + 1)))) ^ 20 by simp [polyBound]]
    have hN : N + 1 ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have hD : D ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) :=
      (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ (by positivity)).trans
        (Nat.le_mul_of_pos_left _ (by omega)))
    have hU : U ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) :=
      (Nat.le_succ _).trans ((Nat.le_mul_of_pos_left _ (by positivity)).trans
        ((Nat.le_mul_of_pos_left _ (by positivity)).trans (Nat.le_mul_of_pos_left _ (by omega))))
    generalize (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) = Q at *
    have hQ : 1 ≤ Q := by omega
    have hN' : N ≤ Q := by omega
    have le20 {i : ℕ} (hi : i ≤ 20 := by omega) : Q ^ i ≤ Q ^ 20 := Nat.pow_le_pow_right hQ hi
    have : 1 ≤ Q ^ 20 := Nat.one_le_pow _ _ hQ
    have hD1 : D ≤ Q ^ 20 := hD.trans (by simpa using le20 (i := 1))
    have : N ≤ Q ^ 20 := hN'.trans (by simpa using le20 (i := 1))
    have : (N + 1) * D ≤ Q ^ 20 :=
      (Nat.mul_le_mul hN hD).trans ((show Q * Q = Q ^ 2 by ring).le.trans le20)
    have : N * D ≤ Q ^ 20 :=
      (Nat.mul_le_mul hN' hD).trans ((show Q * Q = Q ^ 2 by ring).le.trans le20)
    have : D * (U * U) ≤ Q ^ 20 :=
      (Nat.mul_le_mul hD (Nat.mul_le_mul hU hU)).trans
        ((show Q * (Q * Q) = Q ^ 3 by ring).le.trans le20)
    have : ((N + 1) ^ 5) ^ 3 * (U * U) ≤ Q ^ 20 :=
      (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.pow_le_pow_left hN 5) 3)
        (Nat.mul_le_mul hU hU)).trans ((show (Q ^ 5) ^ 3 * (Q * Q) = Q ^ 17 by ring).le.trans le20)
    have : (N + 1) ^ 5 * U ≤ Q ^ 20 :=
      (Nat.mul_le_mul (Nat.pow_le_pow_left hN 5) hU).trans
        ((show Q ^ 5 * Q = Q ^ 6 by ring).le.trans le20)
    have : (N + 1) ^ 5 ≤ Q ^ 20 := (Nat.pow_le_pow_left hN 5).trans le20
    have : ((N + 1) ^ 5) ^ 4 ≤ Q ^ 20 :=
      (Nat.pow_le_pow_left (Nat.pow_le_pow_left hN 5) 4).trans (by ring_nf; exact le_rfl)
    have : G.a * (4 * D) ≤ 4 * G.a * Q ^ 20 :=
      (show G.a * (4 * D) = 4 * G.a * D by ring).le.trans (Nat.mul_le_mul_left _ hD1)
    have : G.p * (4 * D) ≤ 4 * G.p * Q ^ 20 :=
      (show G.p * (4 * D) = 4 * G.p * D by ring).le.trans (Nat.mul_le_mul_left _ hD1)
    have : r + G.b + G.q + G.m₀ + 14 ≤ (r + G.b + G.q + G.m₀ + 14) * Q ^ 20 :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hκ : (1405 + r + 4 * G.a + 4 * G.p + G.b + G.q + G.m₀ + 14) * Q ^ 20 ≤ 2 ^ κ * Q ^ 20 :=
      Nat.mul_le_mul_right _ (hκdef ▸ Nat.lt_two_pow_self.le)
    have : (1405 + r + 4 * G.a + 4 * G.p + G.b + G.q + G.m₀ + 14) * Q ^ 20 =
        1405 * Q ^ 20 + 4 * G.a * Q ^ 20 + 4 * G.p * Q ^ 20 +
          (r + G.b + G.q + G.m₀ + 14) * Q ^ 20 := by ring
    dsimp only [allInstancesNeedP, wordRS, offline32Need]
    refine ⟨by omega, by omega, by omega⟩
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ =>
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

open Classical in
theorem allInstancesP_solves {G : RatParams} {r : ℕ} (hfit : FitsRS G r) :
    SolvesN thinTask (programP G r) Proc.allP (allInstancesTimeP G r)
      (allInstancesNeedP G r) := by
  obtain ⟨hpow, htest⟩ := programRS_at G r
  refine ⟨allBody Proc.testRS Proc.offline32P, programP_at G r Proc.allP,
    fun Q lim d x μ fr hpre hok => ?_⟩
  have ok : (allInstancesNeedP G r [x.N, x.D, x.w, x.U]).Ok lim fr d := hok
  have okO : (offline32Need G x.N x.D x.U).Ok lim fr d :=
    ok.mono (by change _ ≤ wordRS r x.N x.D + (100 + x.D * (x.U * x.U)) + _; omega)
      (by change fr + _ ≤ fr + (x.N + 1 + _); omega) (by change d + _ ≤ d + (2 + _); omega)
  have hword := ok.word
  have hcells := ok.cells
  have hdepth := ok.depth
  simp only [allInstancesNeedP] at hword hcells hdepth
  have hfits : ∀ n : ℕ, n ≤ wordRS r x.N x.D + (100 + x.D * (x.U * x.U)) → (n : ℤ) ≤ lim.word :=
    fun n hn => le_trans (by exact_mod_cast (by omega)) hword
  have h100 := hfits 100 (by omega)
  have hroom : fr + x.N + 1 ≤ lim.space := by omega
  clear hword hcells
  change Ends lim (programP G r ++ Q) d (allBody Proc.testRS Proc.offline32P)
    ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
    (tTestRS r + 64 + if x.D ^ r ≤ x.N then tOffline32P cShared30 G x.N x.D x.w
      else 40 * ((x.w + 1) * (x.D + 1))) _
  unfold allBody
  refine Ends.callToThen (testRS_meets r
    (by rw [programP, List.append_assoc]; exact getElem?_append_of_eq_some htest _)
    (by rw [programP, List.append_assoc]; exact getElem?_append_of_eq_some hpow _)
    (by omega) x.N x.D hpre.N_pos hpre.D_pos (hfits _ (by omega)) μ) ?_ (hT := by simp; omega)
  rintro r' μ ⟨rfl, hr⟩
  refine Ends.iteLast (fun hpos => ?_) (fun hneg => ?_)
  · have hreg : x.D ^ r ≤ x.N := by
      rcases hr with ⟨-, h⟩ | ⟨rfl, -⟩
      · exact h
      · simp at hpos
    rw [ite_eq_left hreg]
    exact Ends.callTo (offline32P_meets_thinTask ((offline32P_programP G r lim).append Q)
      hpre (hfit _ _ hreg) okO) fun _ _ h => h
  · have hreg : ¬ x.D ^ r ≤ x.N := by
      rcases hr with ⟨rfl, -⟩ | ⟨-, h⟩
      · simp at hneg
      · exact h
    rw [ite_eq_right hreg]
    have hbrute : Meets lim (programP G r ++ Q) Sec2.pThinBrute (d + 1)
        [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ (40 * ((x.w + 1) * (x.D + 1)))
        fun r μ' => thinTask.Post x μ fr r μ' :=
      .of_body (by rw [programP_eq_base58]; exact at_base58 rfl _) (Sec2.thinBrute_spec
        ⟨ok.space, by exact_mod_cast h100⟩ x μ fr (x.U : ℤ) hpre hroom (hfits _ (by omega)))
    exact Ends.callTo hbrute fun _ _ h => h

open Classical in
theorem thinClaimP_of_offlineWithinT {G : RatParams} {r : ℕ} {ε γ q : ℝ} (hr : 1 ≤ r)
    (hfit : FitsRS G r) (hε : ε ≤ 1 / (r : ℝ))
    (h : OfflineWithinT (tOffline32P cShared30 G) ε γ q) : ThinClaim lightModel ε γ q := by
  obtain ⟨A, hA⟩ := h.add_const (tTestRS r + 64)
  refine ⟨A, fun N D₀ w _ => (allInstancesTimeP G r [N, D₀, w, 0] : ℝ),
    ⟨_, _, _, _, allInstancesNeedP_poly G r, allInstancesP_solves hfit,
      fun N D₀ w w' U u _ _ _ hw _ => ?_⟩,
    fun N D₀ w u hN hD hDN => ?_⟩
  · change (allInstancesTimeP G r [N, D₀, w, U] : ℝ) ≤ (allInstancesTimeP G r [N, D₀, w', 0] : ℝ)
    simp only [allInstancesTimeP]
    split_ifs
    · have := Nat.mul_le_mul_right (tQuery31 G D₀ + 30) hw
      unfold tOffline32P
      exact_mod_cast (by omega)
    · have := Nat.mul_le_mul_right (D₀ + 1) (show w + 1 ≤ w' + 1 by omega)
      exact_mod_cast (by omega : tTestRS r + 64 + 40 * ((w + 1) * (D₀ + 1)) ≤ _)
  · have htime : (allInstancesTimeP G r [N, D₀, w, 0] : ℝ)
        = (tOffline32P cShared30 G N D₀ w : ℝ) + 400 + ((tTestRS r + 64 : ℕ) : ℝ) - 400 := by
      simp only [allInstancesTimeP, ite_eq_left (pow_le_pow_of_le_rpow hr hε hN hDN)]
      push_cast
      ring
    change (allInstancesTimeP G r [N, D₀, w, 0] : ℝ) ≤ _
    rw [htime]
    linarith [hA N D₀ w hN hD hDN]

end ImprovedExponents
