module

public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Lang.Lib.Logs
public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks
public import ThreeSumApsp.Util.Ceil
public import ThreeSumApsp.Util.Flag
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.BitSearch
public import ThreeSumApsp.Util.Asymptotics.LogU
public import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.Host
public import ThreeSumApsp.TimeClaims.Sec3.Definitions
public import ThreeSumApsp.Programs.Sec3.Theorem21a.Convolution.Host
public import PaperStatements
public import ThreeSumApsp.Lang.Logic
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Machine.Solving
public import ThreeSumApsp.Lang.Compiler.Simulation
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Passes
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.NeedPolynomial
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Arrays
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Costs
public import ThreeSumApsp.Sec4.Corollary31
public import ThreeSumApsp.Sec4.Table2.LogBounds
public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Log
public import ThreeSumApsp.Sec4.Corollary31.RationalParameters
public import ThreeSumApsp.Lang.TopProcedure
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Program

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The (min,+)-product from Negative Triangle: the claim

[VW18, Theorem 4.2] in the form needed for Theorem 21(b).  The three hosts
(finding from deciding, all pairs from finding, the product from all pairs) are composed, and their
time functions are bounded with the two properties of a good running time: T(s)/s is nondecreasing,
and T(s) ≥ s² (1 + log u).

Each host has one bound, up to a constant factor: finding costs O(T(n)) (findTime_dominated: the
side lengths of the search add up to at most 2n, and T(h) ≤ (h/n) T(n)); all pairs cost
O(n² T(⌈n^{1/3}⌉)) (pairsTime_dominated: there are O(n²) rounds, rounds_le); the product costs
O(log u) calls (mpTime_dominated, mpRounds_le).  claim_VW18_Theorem_4_2 puts the three together.
-/


/-! ## Good running times -/

namespace ThreeSumApsp.GoodTime

variable {T : ℕ → ℝ → ℝ}

end ThreeSumApsp.GoodTime

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace MinPlusFromNeg

/-! ## The parameters of a bound -/

/-! ## Finding from deciding -/

/-! ## All pairs from finding -/

/-! ## The product from all pairs -/

/-- The number of rounds of the search is O(log u). -/
theorem mpRounds_le {U : ℕ} (hU : 1 ≤ U) {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (mpRounds U : ℝ) ≤ 8 * logU u := by
  have : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hhalf := Real.one_half_lt_log_two
  have hpow : 2 ^ Nat.log 2 (4 * U) ≤ 4 * U := Nat.pow_log_le_self 2 (by omega)
  -- ⌊log₂ 4U⌋ log 2 ≤ log 4U = 2 log 2 + log U
  have hlog : (Nat.log 2 (4 * U) : ℝ) * Real.log 2 ≤ Real.log (4 * U) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_four] at hlog
  have : Real.log U ≤ logU u := (Real.log_le_log (by positivity) hu).trans
    (log_le_logU (by linarith))
  have := log_two_le_logU u
  have : (Nat.log 2 (4 * U) : ℝ) * (1 / 2) ≤ (Nat.log 2 (4 * U) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hhalf.le (Nat.cast_nonneg _)
  simp only [mpRounds]
  push_cast
  -- ⌊log₂ 4U⌋ / 2 ≤ 3 logU u, and 1 ≤ 2 logU u
  linarith

end MinPlusFromNeg


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# APSP from the (min,+)-product: the claim

The running time of the host (`apTime`, `isHost_ap`) in the form of the claim
`ApspFromMinPlus`: `⌈log₂ n⌉ + 1` times the sum of the time of a (min,+)-product of
matrices whose entries are bounded by `3nu` and of `O(n² (1 + log(nu)))` (for Theorem 21(b)).
-/




/-- APSP from the (min,+)-product, for programs of the light language. -/
theorem claim_apspFromMinPlus : Claim.ApspFromMinPlus lightModel := by
  refine ⟨3, 135, by norm_num, fun T hT => isHost_ap.solvedIn hT fun Tn hTn n U u hn hU hu => ?_⟩
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hτ : (Tn n (3 * (n * U)) : ℝ) ≤ T n (3 * ((n : ℝ) * u)) := by
    refine hTn n (3 * (n * U)) _ hn (by have := Nat.mul_pos hn hU; omega) ?_
    push_cast
    have : (n : ℝ) * U ≤ n * u := mul_le_mul_of_nonneg_left hu (by positivity)
    linarith
  have : 0 ≤ logU (3 * ((n : ℝ) * u)) :=
    Real.log_nonneg (le_trans (by norm_num) (le_max_right _ _))
  have hτ0 : 0 ≤ T n (3 * ((n : ℝ) * u)) := le_trans (by positivity) hτ
  have hc0 : (0 : ℝ) ≤ (Nat.clog 2 n : ℝ) := by positivity
  have hns : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hs1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hsℓ : 0 ≤ (n : ℝ) ^ 2 * logU (3 * ((n : ℝ) * u)) := by positivity
  simp only [apTime]
  push_cast
  rw [← sq (n : ℝ)]
  -- `t ≤ τ` are the time of the solver and its bound, `ℓ = log (3nu)`, `c` is the number of rounds
  -- and `s = n²`
  generalize (Tn n (3 * (n * U)) : ℝ) = t at hτ ⊢
  generalize T n (3 * ((n : ℝ) * u)) = τ at hτ hτ0 ⊢
  generalize logU (3 * ((n : ℝ) * u)) = ℓ at hsℓ ⊢
  generalize (Nat.clog 2 n : ℝ) = c at hc0 ⊢
  generalize (n : ℝ) ^ 2 = s at hns hs1 hsℓ ⊢
  have hround : t + 23 * s + 29 ≤ τ + 135 * (s * (1 + ℓ)) := by linarith
  have : 53 * s + 17 * n + 65 ≤ τ + 135 * (s * (1 + ℓ)) := by linarith
  calc c * (t + 23 * s + 29) + 53 * s + 17 * n + 65
      ≤ c * (τ + 135 * (s * (1 + ℓ))) + (τ + 135 * (s * (1 + ℓ))) := by
        linarith [mul_le_mul_of_nonneg_left hround hc0]
    _ = (c + 1) * (τ + 135 * (s * (1 + ℓ))) := by ring

end Light.Sec3

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Running-time claims of Section 3.4: Theorems 21 and 22

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".  They
are deductions between running-time sentences: those of the paper for Theorem 22, and for
Theorem 21, which the paper cites, those of the route taken here.

* Theorem 21(a) from two reductions, [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]:
  `Theorem21a.of_CH20_VW13`.  The sizes, numbers of instances and extra times compose
  by the rules for `n^{a+o(1)}`.
* Theorem 21(b) for the (min,+)-product from [VW13, Theorem 3.3] and [VW18, Theorem 4.2]:
  `Theorem21b.minPlus_of_VW13_VW18`.  The time of the first reduction is again a good
  time (`GoodTime.mul_logU`), and `log (cU) = O(log U)` (`dominated_logU_mul`).
* Theorem 21(b) for APSP by repeated squaring: `Theorem21b.apsp_of_minPlus`, whose
  arithmetic is `dominated_repeatedSquaring`.
* "Plug Theorem 19 into Theorem 21": `threeSum_of_uniform_theorem_21a`,
  `minPlus_of_uniform_theorem_21b`, `apsp_of_uniform_theorem_21b`.
* Theorem 22: the roundings such as `n^{2-1/1296+o(1)} ≤ O(n^{1.99923})`
  (`Claim.SolvedAlongPow.mono`).
-/


namespace ThreeSumApsp

/-! ## Theorem 21(a) -/

/-- Theorem 21(a) from two reductions: [CH20, Theorem 5.1] followed by [VW13, Theorem 4.3]. -/
theorem Theorem21a.of_CH20_VW13 (M : DetTimeModel) (hCH : Claim.CH20_Theorem_5_1 M)
    (hVW : Claim.VW13_Theorem_4_3 M) : Claim.Theorem_21a M := by
  obtain ⟨c, E₂, Num₂, size₂, hc, hE₂, hNum₂, hsize₂, hsize₂_pos, hVW⟩ := hVW
  intro κ hκ
  obtain ⟨E₁, Num₁, mag₁, N, c', κ', hE₁, hNum₁, hN, hpos, hCH⟩ := hCH κ hκ
  have hN' := hN.isPowLittleO
  have hwords : IsPowLittleO (fun n : ℕ => 1 + logU (mag₁ n)) 0 :=
    ((isPowPolylog_const 1).add (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).isPowLittleO
  refine ⟨fun n => E₁ n + Num₁ n * (E₂ (N n) * (1 + logU (mag₁ n))), fun n => Num₁ n * Num₂ (N n),
    fun n => c * mag₁ n, fun n => size₂ (N n), c * c', κ', ?_, ?_, ?_, fun n hn => ?_,
    fun T hT => ?_⟩
  · -- the extra time: `Õ(n^{3/2}) + Õ(1) · N^{3/2+o(1)} · Õ(1)`
    exact hE₁.isPowLittleO.add ((hNum₁.isPowLittleO.mul
      ((hE₂.comp hN' (by norm_num) (by norm_num)).mul hwords)).mono (by norm_num))
  · -- the number of instances: `Õ(1) · O(N^{1/2})`
    exact (hNum₁.isPowLittleO.mul
      (hNum₂.isPowLittleO.comp hN' (by norm_num) (by norm_num))).mono (by norm_num)
  · -- their size: `O(N^{1/2})`
    exact (hsize₂.isPowLittleO.comp hN' (by norm_num) (by norm_num)).mono (by norm_num)
  · obtain ⟨hN1, hmag1, hmag⟩ := hpos n hn
    refine ⟨hsize₂_pos _ hN1, one_le_mul_of_one_le_of_one_le hc hmag1, ?_⟩
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmag (zero_le_one.trans hc)
  · obtain ⟨T', hT', hb⟩ := hCH _ (hVW T hT)
    exact ⟨T', hT', fun n hn => (hb n hn).trans (le_of_eq (by ring))⟩

/-! ## Theorem 21(b): the (min,+)-product -/

/-! ## Theorem 21(b): APSP -/

/-! ## "Plug Theorem 19 into Theorem 21"

The time of Theorem 19 is `uniformTime K δ e s u = K s^{3-δ} (log s + 1)^e (1 + log u)²`.
Theorem 21 evaluates it at sizes `s(n)` and bounds `u(n) ≤ c n^κ` on the numbers, and multiplies it
by powers of `n` and logarithms.  So each bound is a product of functions of known classes. -/

/-- "Plug Theorem 19 into Theorem 21", 3SUM, in general form: with exponent `3 - δ` for Exact
Triangle the time for 3SUM is `n^{2-δ/2+o(1)}`. -/
theorem threeSum_of_uniform_theorem_21a (M : DetTimeModel) {δ : ℝ} (e : ℕ) (hδ1 : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform M δ e) (h21 : Claim.Theorem_21a M) {a : ℝ}
    (ha : 2 - δ / 2 < a) : Claim.SolvedAlongPow M.threeSum UpperBigOPow a := by
  obtain ⟨K, -, hex⟩ := hu
  intro κ hκ
  obtain ⟨E, Num, mag, size, c', κ', hE, hNum, hsize, hpos, h⟩ := h21 κ hκ
  obtain ⟨T', hT', hb⟩ := h _ hex
  have hsizes := (isPowPolylog_rpow_mul_log_add_one_pow (3 - δ) e).isPowLittleO.comp hsize
    (by linarith) (by norm_num)
  have hwords := (((isPowPolylog_const 1).add
    (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).pow 2).isPowLittleO
  have htotal : IsPowLittleO (fun n => E n + Num n * uniformTime K δ e (size n) (mag n))
      (2 - δ / 2) :=
    (hE.mono (by linarith)).add
      ((hNum.mul ((hsizes.mul hwords).const_mul K)).mono (le_of_eq (by push_cast; ring)))
  exact ⟨T', hT', (htotal.isBigOPow ha).upperBigOPow.mono_left (Filter.eventually_atTop.2 ⟨1, hb⟩)⟩

/-! ## Theorem 22 -/

/-- The roundings of Theorem 22, such as "n^{2-1/1296+o(1)} ≤ O(n^{1.99923})", at the level of
claims: an inclusion between two classes of running times carries over to the claims. -/
theorem Claim.SolvedAlongPow.mono {S : (ℕ → ℝ → ℝ) → Prop} {Cls Cls' : (ℕ → ℝ) → ℝ → Prop}
    {a b : ℝ} (h : Claim.SolvedAlongPow S Cls a) (hCls : ∀ f, Cls f a → Cls' f b) :
    Claim.SolvedAlongPow S Cls' b := fun κ hκ =>
  let ⟨T, hT, hb⟩ := h κ hκ
  ⟨T, hT, hCls _ hb⟩

end ThreeSumApsp

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Convolution-3SUM from Exact Triangle: the claim

Theorem 21(a), after [VW13, Theorem 4.3].  The arithmetic that turns the
host `isHost_c3` into the transfer of running times: if Exact Triangle is solved in time T, then
Convolution-3SUM on N numbers of absolute value at most u is solved in time
O(N^{3/2}) (1 + log u) + 2 (⌊√N⌋ + 1) T(⌊√N⌋ + 1, 3u) (`c3_solvedIn_explicit`,
`claim_VW13_Theorem_4_3`).

The host's own work is a cubic polynomial in ⌊√N⌋ (`exists_c3Own_le`), and the instances have
⌊√N⌋ + 1 ≤ 2 √N vertices per part (`natSqrt_succ_le`).
-/


namespace Light.Sec3

open ThreeSumApsp

/-- `⌊√N⌋ + 1 ≤ 2 N^{1/2}` for `N ≥ 1`. -/
theorem natSqrt_succ_le {N : ℕ} (hN : 1 ≤ N) :
    ((Nat.sqrt N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  have : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := Real.nat_sqrt_le_real_sqrt
  have : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast hN)
  push_cast
  linarith

/-- `⌊√N⌋ + 1 = O(N^{1/2})`. -/
theorem isBigOPow_natSqrt_succ :
    IsBigOPow (fun N : ℕ => ((Nat.sqrt N + 1 : ℕ) : ℝ)) (1 / 2) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact natSqrt_succ_le hN

/-- The host's own work: its time over a solver that takes no time. -/
def c3Own (N : ℕ) : ℕ := c3Time (fun _ _ => 0) N 0

/-- The time of the host is its own work and 2 (⌊√N⌋ + 1) runs of the solver. -/
theorem c3Time_eq (T : ℕ → ℕ → ℕ) (N U : ℕ) :
    c3Time T N U = c3Own N + 2 * (Nat.sqrt N + 1) * T (Nat.sqrt N + 1) (2 * U + 1) := by
  unfold c3Own c3Time c3RoundTime
  ring

/-- The host's own work is a cubic polynomial in ⌊√N⌋, so it is O(N^{3/2}). -/
theorem exists_c3Own_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → (c3Own N : ℝ) ≤ C * (N : ℝ) ^ (3 / 2 : ℝ) := by
  -- powers of 2 √N
  let s : Scale ℕ (Fin 1) := .ofBases (1 ≤ ·) (fun _ N => 2 * (N : ℝ) ^ (1 / 2 : ℝ)) fun _ N hN =>
    le_trans (by exact_mod_cast Nat.le_add_left 1 (Nat.sqrt N)) (natSqrt_succ_le hN)
  have hside : s.SoftO (fun N => Nat.sqrt N + 1) _ := .of_le_base 0 fun _ hN => natSqrt_succ_le hN
  have hown : s.SoftO c3Own ![3] := by
    unfold c3Own c3Time c3RoundTime convFillTime
    growth [hside, hside.of_le fun N _ => Nat.le_succ (Nat.sqrt N)]
  obtain ⟨C, hC, hle⟩ := hown.dominated fun _ _ => rfl
  refine ⟨C * 8, by positivity, fun N hN => (hle N hN).trans_eq ?_⟩
  have hpow : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 3 = (N : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul N.cast_nonneg]
    norm_num
  simp only [Scale.mon, s, Scale.ofBases, Fin.prod_univ_one, Matrix.cons_val_zero, mul_pow, hpow]
  ring

/-- Convolution-3SUM from Exact Triangle, with the explicit bound, where C is the constant of the
host's own work.  The weights of the instances are bounded by 2U + 1 ≤ 3u, because 1 ≤ U ≤ u.  The
factor 1 + log u is not needed here; it is the form in which the claim is stated. -/
theorem c3_solvedIn_explicit {C : ℝ} (hC : 0 ≤ C)
    (hown : ∀ N : ℕ, 1 ≤ N → (c3Own N : ℝ) ≤ C * (N : ℝ) ^ (3 / 2 : ℝ)) {T : ℕ → ℝ → ℝ}
    (hT : SolvedIn etTask T) :
    SolvedIn c3Task fun N u => C * (N : ℝ) ^ (3 / 2 : ℝ) * (1 + logU u) +
      2 * ((Nat.sqrt N + 1 : ℕ) : ℝ) * T (Nat.sqrt N + 1) (3 * u) := by
  refine isHost_c3.solvedIn hT fun Tn hTn N U u hN hU hu => ?_
  have : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hsolver : (Tn (Nat.sqrt N + 1) (2 * U + 1) : ℝ) ≤ T (Nat.sqrt N + 1) (3 * u) :=
    hTn _ _ _ (by omega) (by omega) (by push_cast; linarith)
  have : 0 ≤ logU u := Real.log_nonneg (le_trans (by norm_num) (le_max_right u 2))
  rw [c3Time_eq]
  push_cast
  -- the host's own work, and 2 (⌊√N⌋ + 1) runs of the solver
  exact add_le_add ((hown N hN).trans (le_mul_of_one_le_right (by positivity) (by linarith)))
    (mul_le_mul_of_nonneg_left hsolver (by positivity))

/-- [VW13, Theorem 4.3] for programs of the light language: Convolution-3SUM from Exact Triangle. -/
theorem claim_VW13_Theorem_4_3 : Claim.VW13_Theorem_4_3 lightModel :=
  let ⟨C, hC, hown⟩ := exists_c3Own_le
  ⟨3, fun N => C * (N : ℝ) ^ (3 / 2 : ℝ), fun N => 2 * ((Nat.sqrt N + 1 : ℕ) : ℝ),
    fun N => Nat.sqrt N + 1, by norm_num,
    IsBigOPow.isPowLittleO (Asymptotics.isBigO_const_mul_self _ _ _),
    isBigOPow_natSqrt_succ.const_mul_left 2, isBigOPow_natSqrt_succ, fun N _ => Nat.le_add_left 1 _,
    fun _ hT => c3_solvedIn_explicit hC hown hT⟩

end Light.Sec3

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Paths of the end statement and walks with weights in `WithTop ℤ`

The end statement speaks of a directed graph as a function into `Option ℤ` and of
`EndStatement.Path`, an inductive predicate.  The definitions for APSP in `PaperStatements.lean`
speak of weights in `WithTop ℤ`, of walks as lists of vertices, and of `IsDistanceMatrix`.  This
file shows that the two agree.

* A missing edge is the weight `⊤` (`toTop`).
* A path of weight `d` is a walk of weight `d`, and a walk of finite weight is a path
  (`exists_walk_of_path`, `path_of_walk`).
* So "no negative cycles" carries over (`noNegativeCycle_toTop`), and a distance matrix has `⊤`
  where there is no path and the least weight of a path elsewhere (`not_path_of_dist_eq_top`,
  `isLeast_path_of_dist_eq_coe`).
* `reachable_or_not` says this of two numbers that are written down for a pair of vertices, and
  `output_apsp` is the output condition of `EndStatement.APSP`.
-/


namespace ThreeSumApsp

open EndStatement (Path)

variable {n : ℕ} {w : Fin n → Fin n → Option ℤ}

/-- An optional weight, as a weight or `⊤`. -/
@[expose] def toTop : Option ℤ → WithTop ℤ
  | some z => (z : WithTop ℤ)
  | none => ⊤

/-- A path of weight `d` is a walk of weight `d`. -/
theorem exists_walk_of_path {i j : Fin n} {d : ℤ} (h : Path w i j d) :
    ∃ rest : List (Fin n), walkEnd i rest = j ∧
      walkWeight (fun a b => toTop (w a b)) i rest = (d : WithTop ℤ) := by
  induction h with
  | nil i => exact ⟨[], rfl, rfl⟩
  | @cons i j k d e hd _ ih =>
    obtain ⟨rest, hend, hw⟩ := ih
    refine ⟨j :: rest, hend, ?_⟩
    rw [walkWeight, hw, hd]
    rfl

/-- A walk of finite weight `d` is a path of weight `d`. -/
theorem path_of_walk : ∀ (rest : List (Fin n)) (i : Fin n) (d : ℤ),
    walkWeight (fun a b => toTop (w a b)) i rest = (d : WithTop ℤ) → Path w i (walkEnd i rest) d
  | [], i, d, h => by
    obtain rfl : d = 0 := by
      rw [walkWeight] at h
      exact_mod_cast h.symm
    exact .nil i
  | k :: rest, i, d, h => by
    rw [walkWeight] at h
    cases hk : w i k with
    | none => simp [hk, toTop] at h
    | some a =>
      cases hr : walkWeight (fun a b => toTop (w a b)) k rest with
      | top => simp [hr] at h
      | coe b =>
        rw [hk, hr] at h
        obtain rfl : d = a + b := by
          have : ((a + b : ℤ) : WithTop ℤ) = (d : WithTop ℤ) := h
          exact_mod_cast this.symm
        exact .cons hk (path_of_walk rest k b hr)

/-- No closed path of negative weight: no closed walk of negative weight. -/
theorem noNegativeCycle_toTop (hneg : ∀ i d, Path w i i d → 0 ≤ d) :
    NoNegativeCycle fun i j => toTop (w i j) := by
  intro i rest hend
  cases hw : walkWeight (fun a b => toTop (w a b)) i rest with
  | top => exact le_top
  | coe z =>
    have hp := path_of_walk rest i z hw
    rw [hend] at hp
    exact_mod_cast hneg i z hp

variable {dist : Fin n → Fin n → WithTop ℤ}

/-- The distance is at most the weight of every path. -/
theorem dist_le_of_path (hdist : IsDistanceMatrix (fun i j => toTop (w i j)) dist)
    {i j : Fin n} {d : ℤ} (hp : Path w i j d) : dist i j ≤ (d : WithTop ℤ) :=
  (hdist i j).2 (exists_walk_of_path hp)

/-- Where the distance is `⊤` there is no path. -/
theorem not_path_of_dist_eq_top (hdist : IsDistanceMatrix (fun i j => toTop (w i j)) dist)
    {i j : Fin n} (htop : dist i j = ⊤) (d : ℤ) : ¬ Path w i j d := by
  intro hp
  have hle := dist_le_of_path hdist hp
  rw [htop] at hle
  exact absurd hle (by simp)

/-- A finite distance is the weight of a path, and no path is lighter. -/
theorem isLeast_path_of_dist_eq_coe (hdist : IsDistanceMatrix (fun i j => toTop (w i j)) dist)
    {i j : Fin n} {z : ℤ} (hz : dist i j = (z : WithTop ℤ)) :
    Path w i j z ∧ ∀ e, Path w i j e → z ≤ e := by
  obtain ⟨rest, hend, hw⟩ := (hdist i j).1
  rw [hz] at hw
  have hp := path_of_walk rest i z hw
  rw [hend] at hp
  refine ⟨hp, fun e he => ?_⟩
  have hle := dist_le_of_path hdist he
  rw [hz] at hle
  exact_mod_cast hle

/-- Two numbers written down for the pair `(i, j)` as APSP asks: 0 if the distance is `⊤`, and 1 and
the distance otherwise.  Then either the first is 1 and the second is the least weight of a path, or
the first is 0 and there is no path. -/
theorem reachable_or_not (hdist : IsDistanceMatrix (fun i j => toTop (w i j)) dist) {i j : Fin n}
    {flag d : ℤ} (htop : dist i j = ⊤ → flag = 0)
    (hfin : ∀ z : ℤ, dist i j = (z : WithTop ℤ) → flag = 1 ∧ d = z) :
    (flag = 1 ∧ Path w i j d ∧ ∀ e, Path w i j e → d ≤ e) ∨ (flag = 0 ∧ ∀ e, ¬ Path w i j e) := by
  cases hd : dist i j with
  | top => exact Or.inr ⟨htop hd, not_path_of_dist_eq_top hdist hd⟩
  | coe z =>
    obtain ⟨hflag, rfl⟩ := hfin z hd
    exact Or.inl ⟨hflag, isLeast_path_of_dist_eq_coe hdist hd⟩

/-- The output condition of `EndStatement.APSP` is the either-or of `reachable_or_not` for every
pair of vertices. -/
theorem output_apsp (x : EndStatement.APSP.Instance n) (out : ℕ → ℤ)
    (h : ∀ i j : Fin n,
      (out (2 * (i.val * n + j.val)) = 1 ∧ Path x.1 i j (out (2 * (i.val * n + j.val) + 1)) ∧
          ∀ e, Path x.1 i j e → out (2 * (i.val * n + j.val) + 1) ≤ e) ∨
        (out (2 * (i.val * n + j.val)) = 0 ∧ ∀ e, ¬ Path x.1 i j e)) :
    EndStatement.APSP.output x out := h

end ThreeSumApsp

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Two programs in one: relocation of procedures

A program grows by appending procedures.  To put two programs, each with its own numbering of
procedures, into one, the second is placed behind the first (`Program.behind`), and the numbers of
the procedures that it calls are shifted by the length of the first (`Stmt.shift`).

A run of a statement in P is then a run of the shifted statement, with the same states and the
same number of steps (`Exec.shift`, an induction on the run in which only the case of a call has
anything to do: `Program.getElem?_behind_right`).  So everything proved with `Ends` carries over
(`Ends.shift`, `Ends.shift_append`).
-/


namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The statement with n added to the number of every procedure that it calls. -/
def Stmt.shift (n : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .set x e => .set x e
  | .store a e => .store a e
  | .seq s t => .seq (s.shift n) (t.shift n)
  | .ite c s t => .ite c (s.shift n) (t.shift n)
  | .while c s => .while c (s.shift n)
  | .call p args x => .call (p + n) args x

/-- The program P placed behind the program Q. -/
def Program.behind (Q P : Program) : Program := Q ++ P.map (Stmt.shift Q.length)

/-- Procedure p of P is procedure `p + Q.length` of P placed behind Q, with its calls
shifted. -/
theorem Program.getElem?_behind_right (Q : Program) {p : ℕ} {body : Stmt} (h : P[p]? = some body) :
    (Program.behind Q P)[p + Q.length]? = some (body.shift Q.length) := by
  rw [Program.behind, List.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
    List.getElem?_map, h]
  rfl

/-- **Relocation.**  A run in P is a run, with the same states and the same number of steps, of
the shifted statement in P placed behind Q. -/
theorem Exec.shift {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (Q : Program) :
    Exec lim (Program.behind Q P) d (s.shift Q.length) σ σ' c := by
  induction h with
  | skip => exact .skip
  | set h => exact .set h
  | store h₁ h₂ h₃ => exact .store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact .iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact .iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact .whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact .whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact .call h₁ (Program.getElem?_behind_right Q h₂) h₃ ih

/-- What is proved about a statement in P holds for the shifted statement in P placed behind
Q. -/
theorem Ends.shift {s σ T post} (h : Ends lim P d s σ T post) (Q : Program) :
    Ends lim (Program.behind Q P) d (s.shift Q.length) σ T post := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.shift Q, hc, hq⟩

/-- The same with more procedures appended behind. -/
theorem Ends.shift_append {s σ T post} (h : Ends lim P d s σ T post) (Q R : Program) :
    Ends lim (Program.behind Q P ++ R) d (s.shift Q.length) σ T post :=
  (h.shift Q).append R

end Light

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Two algorithms for Exact Triangle and a threshold on the number of vertices

For every threshold n₀ there is a constant C₀ such that, if Exact Triangle is solved in time T₁ and
in time T₂, then it is solved in time T₁ + C₀ for n < n₀ and T₂ + C₀ for n ≥ n₀.  This is
`Closure.ChooseBySize`, with "Exact Triangle is solved in time T" read as `SolvedIn etTask T`
(`closure_chooseBySize`).  It is used in the proof of Theorem 19, where the bounds hold
for large n only.

Two solvers are put into one program, the second behind the first (`solves_behind`), and one more
procedure looks at the number of vertices and calls the first solver below a fixed threshold n₀ and
the second one from the threshold on (`bySize_spec`).  The need stays polynomial
(`polyNeed_bySize`).
-/


namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-- choose(n, U, ab, bc, ac, fr): calls procedure p₁ if n < n₀, and procedure p₂ if not, on the same
arguments: the number n of vertices in a part, the bound U on the weights, the addresses ab, bc, ac
of the three matrices of weights, and the free pointer fr. -/
def bySizeBody (n₀ p₁ p₂ : ℕ) : Stmt :=
  .ite (v 0 <' k n₀) (.call p₁ [v 0, v 1, v 2, v 3, v 4, v 5] 0)
    (.call p₂ [v 0, v 1, v 2, v 3, v 4, v 5] 0)

/-- The number of steps of choose. -/
def bySizeTime (n₀ : ℕ) (T₁ T₂ : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ := (if n < n₀ then T₁ n U else T₂ n U) +
    12

/-- What choose needs: a word for the threshold, one more level of calls, and what the two solvers
need. -/
def bySizeNeed (n₀ : ℕ) (r₁ r₂ : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨n₀ + (r₁ n U).word + (r₂ n U).word, (r₁ n U).cells + (r₂ n U).cells, 1 + (r₁ n U).depth +
    (r₂ n U).depth⟩

namespace ChooseHost

/-- A solver stays a solver, with its number shifted, when its program is placed behind another
program. -/
theorem solves_behind {task : Task} {P : Program} {p : ℕ} {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : Solves task P p T need)
    (Q : Program) : Solves task (Program.behind Q P) (p + Q.length) T need := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body.shift Q.length, Program.getElem?_behind_right Q hp, fun R lim d x μ fr hpre hok =>
    ?_⟩
  have := hb [] lim d x μ fr hpre hok
  rw [List.append_nil] at this
  exact this.shift_append Q R

/-- **choose** solves Exact Triangle. -/
theorem bySize_spec {P₀ R : Program} {n₀ p₁ p₂ : ℕ} {T₁ T₂ : ℕ → ℕ → ℕ} {r₁ r₂ : ℕ → ℕ → Need}
    (h₁ : Solves etTask P₀ p₁ T₁ r₁) (h₂ : Solves etTask P₀ p₂ T₂ r₂) {x : TriInst} {μ : ℕ → ℤ}
    {fr : ℕ} (hpre : x.Pre μ fr) (hok : (bySizeNeed n₀ r₁ r₂ x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (bySizeBody n₀ p₁ p₂) ⟨frame (etTask.args x ++ [(fr : ℤ)]), μ⟩
      (bySizeTime n₀ T₁ T₂ x.n x.U) fun σ' => etTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have : ((n₀ + (r₁ x.n x.U).word + (r₂ x.n x.U).word : ℕ) : ℤ) ≤ lim.word := hok.word
  have : d + (1 + (r₁ x.n x.U).depth + (r₂ x.n x.U).depth) ≤ lim.depth := hok.depth
  have hok₁ : (r₁ x.n x.U).Ok lim fr (d + 1) := hok.mono (by simp only [bySizeNeed]; omega)
    (by simp only [bySizeNeed]; omega) (by simp only [bySizeNeed]; omega)
  have hok₂ : (r₂ x.n x.U).Ok lim fr (d + 1) := hok.mono (by simp only [bySizeNeed]; omega)
    (by simp only [bySizeNeed]; omega) (by simp only [bySizeNeed]; omega)
  have hm₁ : Meets lim (P₀ ++ R) p₁ (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, fr] μ (T₁ x.n x.U)
      (etTask.Post x μ fr) := h₁.meets R x fr hpre hok₁
  have hm₂ : Meets lim (P₀ ++ R) p₂ (d + 1) [x.n, x.U, x.ab, x.bc, x.ac, fr] μ (T₂ x.n x.U)
      (etTask.Post x μ fr) := h₂.meets R x fr hpre hok₂
  change Ends lim (P₀ ++ R) d (bySizeBody n₀ p₁ p₂) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ _ _
  unfold bySizeTime
  -- if n < n₀ then the first solver else the second
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
  · rw [if_pos (show x.n < n₀ by simp at hc; omega)]
    exact Ends.callTo hm₁ fun _ _ h => h
  · rw [if_neg (show ¬ x.n < n₀ by simp at hc; omega)]
    exact Ends.callTo hm₂ fun _ _ h => h

/-- The need of choose is polynomially bounded if the needs of the two solvers are. -/
theorem polyNeed_bySize (n₀ : ℕ) {r₁ r₂ : ℕ → ℕ → Need} (h₁ : PolyNeed r₁) (h₂ : PolyNeed r₂) :
    PolyNeed (bySizeNeed n₀ r₁ r₂) := by
  unfold bySizeNeed
  poly_need [h₁.word, h₁.cells, h₁.depth, h₂.word, h₂.cells, h₂.depth]

end ChooseHost

open ChooseHost

/-- **Two algorithms, chosen by the size of the instance.** -/
theorem closure_chooseBySize : Closure.ChooseBySize lightModel := by
  refine fun n₀ => ⟨12, fun T₁ T₂ hT₁ hT₂ => ?_⟩
  obtain ⟨Q₁, p₁, Tn₁, r₁, hr₁, hs₁, ht₁⟩ := hT₁
  obtain ⟨Q₂, p₂, Tn₂, r₂, hr₂, hs₂, ht₂⟩ := hT₂
  have g₁ : Solves etTask (Program.behind Q₁ Q₂) p₁ Tn₁ r₁ := hs₁.append _
  have g₂ : Solves etTask (Program.behind Q₁ Q₂) (p₂ + Q₁.length) Tn₂ r₂ := solves_behind hs₂ Q₁
  refine ⟨Program.behind Q₁ Q₂ ++ [bySizeBody n₀ p₁ (p₂ + Q₁.length)],
    (Program.behind Q₁ Q₂).length, bySizeTime n₀ Tn₁ Tn₂,
    bySizeNeed n₀ r₁ r₂, polyNeed_bySize n₀ hr₁ hr₂, ?_, fun n U u hn hU hu => ?_⟩
  · refine ⟨bySizeBody n₀ p₁ (p₂ + Q₁.length), by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact bySize_spec g₁ g₂ hpre hok
  · simp only [bySizeTime]
    push_cast
    split_ifs
    · linarith [ht₁ n U u hn hU hu]
    · linarith [ht₂ n U u hn hU hu]

end Light.Sec3

end

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Corollary 15: counting triangles with the thin matrix product, and detecting with counting

Two steps of the proof of Corollary 15, with "the problem is solved in time T" read as
`ThinSolvedIn` and `LopSolvedIn`.

* `Claim.LopCountFromThinProduct`: "Apply Theorem 5 with N = n to the two biadjacency matrices".  An
  instance of #Lop-AE-SparseTri is given by its two biadjacency matrices, so a solver of the thin
  matrix product is a solver of #Lop-AE-SparseTri as it stands, called with U = 1, where U, the
  fourth argument and parameter, is the bound on the entries of the matrices
  (`solvesN_count_of_thin`, `claim_lopCountFromThinProduct`).
* `Claim.LopDetectFromCount`: the counts "are nonzero exactly for the query pairs that lie in a
  triangle".  One more procedure calls the counting solver and replaces every nonzero count by 1
  (`detect_spec`, `claim_lopDetectFromCount`).
-/


namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

namespace LopHosts

/-! ## Bounds -/

/-- One more parameter with the value 1 costs a factor `2^e`. -/
theorem polyBound_snoc_one (s e : ℕ) (ps : List ℕ) :
    polyBound s e (ps ++ [1]) = polyBound (s + e) e ps := by
  simp only [polyBound, List.map_append, List.map_cons, List.map_nil, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one,
    mul_pow, pow_add]
  norm_num
  ring

/-- Twice the bound leaves room for one more. -/
theorem polyBound_le_succ (s e : ℕ) (ps : List ℕ) :
    polyBound s e ps + 1 ≤ polyBound (1 + s) e ps := by
  have := one_le_polyBound s e ps
  rw [← polyBound_mul]
  omega

/-! ## Counting with the thin matrix product -/

/-- A solver of the thin matrix product solves #Lop-AE-SparseTri. -/
theorem solvesN_count_of_thin {P : Program} {p : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (h : SolvesN thinTask P p Tn need) :
    SolvesN lopCountTask P p (fun ps => Tn (ps ++ [1])) fun ps => need (ps ++ [1]) := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body, hp, fun R lim d x μ fr hpre hok => ?_⟩
  obtain ⟨h1, h3⟩ := hpre
  have hpars : thinTask.pars x = lopCountTask.pars x ++ [1] := by
    simp only [thinTask, lopCountTask, List.cons_append, List.nil_append]
    rw [h3]
  have hrun := hb R lim d x μ fr h1 (hpars ▸ hok)
  rwa [hpars] at hrun

/-- A polynomially bounded need stays so when a parameter is fixed to 1. -/
theorem polyNeedN_snoc_one {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN fun ps => need (ps ++ [1]) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨s + e, e, fun ps => ?_⟩
  rw [← polyBound_snoc_one]
  exact h _

end LopHosts

open LopHosts

/-- **Counting common neighbours is a thin matrix product** (Section 3.1). -/
theorem claim_lopCountFromThinProduct : Claim.LopCountFromThinProduct lightModel := by
  refine ⟨0, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P, p, _, _, polyNeedN_snoc_one hneed, solvesN_count_of_thin hsol,
    fun n D w w' hn hD hw => ?_⟩
  have := htime n D w w' 1 1 hn hD le_rfl hw (by norm_num)
  simpa using this

/-! ## Detecting with counting -/

namespace LopArgs

/-- The local variables that hold the arguments of a solver of the thin matrix product or of a
lopsided triangle problem: N, D, w, U, x, y, wi, wj, out, fr. -/
abbrev N : ℕ := 0
@[inherit_doc N] abbrev DD : ℕ := 1
@[inherit_doc N] abbrev W : ℕ := 2
@[inherit_doc N] abbrev U : ℕ := 3
@[inherit_doc N] abbrev X : ℕ := 4
@[inherit_doc N] abbrev Y : ℕ := 5
@[inherit_doc N] abbrev WI : ℕ := 6
@[inherit_doc N] abbrev WJ : ℕ := 7
@[inherit_doc N] abbrev OUT : ℕ := 8
@[inherit_doc N] abbrev FR : ℕ := 9

end LopArgs

open LopArgs in
/-- detect(N, D, w, U, x, y, wi, wj, out, fr): calls the counting solver on the same arguments, then
replaces every nonzero answer by 1.  Local 10 takes the result of the call and is then the
counter. -/
def lopDetectBody (pCount : ℕ) : Stmt :=
  .call pCount [v N, v DD, v W, v U, v X, v Y, v WI, v WJ, v OUT, v FR] 10 ;;
  .for 10 (v W) (.ite (M (v OUT +' v 10) =' k 0) .skip (.store (v OUT +' v 10) (k 1)))

/-- The number of steps of detect, if the counting solver takes Tn; the third parameter is w. -/
def lopDetectTime (Tn : List ℕ → ℕ) (ps : List ℕ) : ℕ := Tn ps + 20 * ps.getD 2 0 + 18

/-- What detect needs: one more level of calls. -/
def lopDetectNeed (need : List ℕ → Need) (ps : List ℕ) : Need :=
  ⟨(need ps).word, (need ps).cells, (need ps).depth + 1⟩

namespace LopHosts

/-- There is one answer for each wanted position. -/
theorem length_thinOut (N D : ℕ) (X Y : List ℤ) {WI WJ : List ℕ} {w : ℕ} (h1 : WI.length = w)
    (h2 : WJ.length = w) : (thinOut N D X Y WI WJ).length = w := by
  simp [thinOut, h1, h2]

/-- **detect** solves Lop-AE-SparseTri. -/
theorem detect_spec {P₀ R : Program} {p : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (hsol : SolvesN lopCountTask P₀ p Tn need) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : lopDetectTask.Pre x μ fr)
    (hok : (lopDetectNeed need (lopDetectTask.pars x)).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (lopDetectBody p) ⟨frame (lopDetectTask.args x ++ [(fr : ℤ)]), μ⟩
      (lopDetectTime Tn (lopDetectTask.pars x))
      fun σ' => lopDetectTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have := hok.space
  have := hok.cells
  have : d + ((need [x.N, x.D, x.w]).depth + 1) ≤ lim.depth := hok.depth
  have := hpre.1.belowOut
  have hlen := length_thinOut x.N x.D x.X x.Y hpre.1.lenWI hpre.1.lenWJ
  have hm : Meets lim (P₀ ++ R) p (d + 1)
      [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr] μ (Tn [x.N, x.D, x.w]) fun _ μ₁ =>
        Seg μ₁ x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ₁ fr x.out x.w :=
    hsol.meets R x hpre (hok.mono le_rfl le_rfl (by
      change d + 1 + (need [x.N, x.D, x.w]).depth ≤ d + ((need [x.N, x.D, x.w]).depth + 1)
      omega))
  change Ends lim (P₀ ++ R) d (lopDetectBody p)
    ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
    (Tn [x.N, x.D, x.w] + 20 * x.w + 18) _
  -- the counts
  refine Ends.callToThen hm fun r μ₁ ⟨hseg, hk⟩ => ?_
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, ∀ i, f i = if μ₁ (x.out + i) = 0 then 0 else 1 := ⟨_, fun _ => rfl⟩
  -- for i < w: the first i counts have been replaced
  refine Ends.forFrame (fun j μ' => μ' = wrote μ₁ x.out f j) x.w wrote_zero.symm ?round ?done
    (hT := by simp; omega)
  case round =>
    rintro j _ hj rfl
    have hread : wrote μ₁ x.out f j (x.out + j) = μ₁ (x.out + j) := wrote_rest (by omega)
    rw [← wrote_succ]
    -- if out[i] ≠ 0 then out[i] := 1
    refine Ends.iteLast (fun hc => Ends.skip ⟨rfl, ?_⟩) fun hc =>
      Ends.storeTo (x.out + j) 1 ⟨rfl, ?_⟩
    · have hc : μ₁ (x.out + j) = 0 := by simpa [hread] using hc
      have e : f j = wrote μ₁ x.out f j (x.out + j) := by rw [hf, if_pos hc, hread, hc]
      rw [e, Function.update_eq_self]
    · have hc : μ₁ (x.out + j) ≠ 0 := by simpa [hread] using hc
      rw [hf, if_neg hc]
  case done =>
    rintro _ rfl
    refine ⟨fun i hi => ?_, fun a ha => (wrote_rest ha.2).trans (hk a ha)⟩
    have hi' : i < x.w := by simpa [hlen] using hi
    rw [List.getElem_map, ← hseg i (by omega), ← hf]
    exact wrote_done hi'

/-- The need of detect is polynomially bounded if that of the counting solver is. -/
theorem polyNeedN_detect {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN (lopDetectNeed need) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨1 + s, e, fun ps => ?_⟩
  have := polyBound_le_succ s e ps
  obtain ⟨a, b, c⟩ := h ps
  simp only [lopDetectNeed]
  omega

end LopHosts


/-- **Detection from counting** (proof of Corollary 15). -/
theorem claim_lopDetectFromCount : Claim.LopDetectFromCount lightModel := by
  refine ⟨20, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P ++ [lopDetectBody p], P.length, lopDetectTime Tn, lopDetectNeed need,
    polyNeedN_detect hneed, ?_, fun n D w w' hn hD hw => ?_⟩
  · refine ⟨lopDetectBody p, by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact detect_spec hsol hpre hok
  · have h1 := htime n D w w' hn hD hw
    have : (w : ℝ) ≤ w' := by exact_mod_cast hw
    simp only [lopDetectTime, List.getD_cons_succ, List.getD_cons_zero]
    push_cast
    linarith

end Light.Sec3

end




open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.Spec

namespace ThreeSumApsp.WordRam

theorem rpow_pow_den {r : ℚ} (hr0 : 0 ≤ r) (n : ℕ) :
    ((n : ℝ) ^ (r : ℝ)) ^ r.den = (n : ℝ) ^ r.num.toNat := by
  have hnum : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg (Rat.num_nonneg.2 hr0))
  have : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hmul : (r : ℝ) * (r.den : ℝ) = ((r.num.toNat : ℕ) : ℝ) := by
    rw [Rat.cast_def, hnum]; field_simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), hmul, Real.rpow_natCast]

noncomputable def stepBound (C a : ℝ) (n : ℕ) : ℕ := ⌈C * ((n : ℝ) ^ a + 1)⌉₊

theorem bigO_stepBound (C : ℝ) {r : ℚ} (hr0 : 0 ≤ r) : EndStatement.BigO (stepBound C r) r := by
  set D := 2 * |C| + 1
  refine ⟨⌈|D| ^ r.den⌉₊, fun n hn => ?_⟩
  have hrpow : (0 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ (r : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by exact_mod_cast hr0)
  have habs : C * ((n : ℝ) ^ (r : ℝ) + 1) ≤ |C| * ((n : ℝ) ^ (r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have : (stepBound C r n : ℝ) < |C| * ((n : ℝ) ^ (r : ℝ) + 1) + 1 :=
    (Nat.cast_le.2 (Nat.ceil_le_ceil habs)).trans_lt (Nat.ceil_lt_add_one (by positivity))
  have hT : (stepBound C r n : ℝ) ≤ D * (n : ℝ) ^ (r : ℝ) := by
    nlinarith [mul_nonneg (abs_nonneg C) (sub_nonneg.2 hone)]
  have hreal : (stepBound C r n : ℝ) ^ r.den ≤ (⌈|D| ^ r.den⌉₊ : ℝ) * (n : ℝ) ^ r.num.toNat :=
    calc (stepBound C r n : ℝ) ^ r.den
        ≤ (|D| * (n : ℝ) ^ (r : ℝ)) ^ r.den :=
          pow_le_pow_left₀ (Nat.cast_nonneg _)
            (hT.trans (mul_le_mul_of_nonneg_right (le_abs_self D) hrpow)) _
      _ = |D| ^ r.den * (n : ℝ) ^ r.num.toNat := by rw [mul_pow, rpow_pow_den hr0]
      _ ≤ (⌈|D| ^ r.den⌉₊ : ℝ) * (n : ℝ) ^ r.num.toNat :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
  exact_mod_cast hreal

end ThreeSumApsp.WordRam

namespace ThreeSumApsp.FromClaims

theorem solvedInTime_of_claim {S : (ℕ → ℝ → ℝ) → Prop} {Q : EndStatement.Problem}
    (hR : ∀ T, S T → Realized Q T) {r : ℚ} (hr0 : 0 ≤ r)
    (h : Claim.SolvedAlongPow S UpperBigOPow r) : Q.SolvedInTime r := by
  intro κ
  obtain ⟨T, hT, C, hb⟩ := h κ (Nat.cast_nonneg κ)
  obtain ⟨P, b, c, hc, hS⟩ := hR T hT κ
  have hg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (r : ℝ) := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨C', hC', hdom⟩ := Dominated.of_eventually_add_one hb hg
  set K : ℝ := c * C' + c
  refine ⟨P, b, stepBound K r, bigO_stepBound K hr0, fun n x hx W hW => ?_⟩
  obtain ⟨t, verdict, m, ht, hexec, hyes, hout⟩ :=
    hS ⟨n, n ^ κ, x, hx⟩ rfl W (by simpa [Admissible] using hW)
  have hU : (((n ^ κ : ℕ) : ℝ)) = (n : ℝ) ^ ((κ : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; push_cast; rfl
  have hcT : c * max (T n ((n ^ κ : ℕ) : ℝ)) 0 ≤ c * (C' * ((n : ℝ) ^ (r : ℝ) + 1)) := by
    rw [hU]
    exact mul_le_mul_of_nonneg_left
      (max_le (hdom n trivial) (mul_nonneg hC' (by linarith [hg n]))) hc
  have ht' : t ≤ stepBound K r n := by
    have : (t : ℝ) ≤ K * ((n : ℝ) ^ (r : ℝ) + 1) := by linarith [ht, mul_nonneg hc (hg n)]
    exact_mod_cast this.trans (Nat.le_ceil _)
  exact ⟨verdict, m, WordRam.exec_mono (c := ⟨0, _⟩) hexec ht', hyes,
    (output_cons m n (Q.input x)).symm ▸ hout⟩

end ThreeSumApsp.FromClaims

namespace Light.Sec3

theorem vecOf_ofFn {n : ℕ} (x : Fin n → ℤ) : vecOf n (List.ofFn x) = x := by
  funext i
  simp [vecOf, List.getD_eq_getElem?_getD]

def threeSumInst (x : Bounded EndStatement.ThreeSum) : s3Task.Inst := ⟨x.n, x.U, 1, List.ofFn x.x⟩

theorem realized_threeSum (T : ℕ → ℝ → ℝ) (h : SolvedIn s3Task T) :
    Realized EndStatement.ThreeSum T :=
  ({ args := [v 1, v 2, k 1, v 1 +' k 1]
     inst := threeSumInst
     fr x := x.n + 1
     size_eq _ := rfl
     bound_eq _ := rfl
     fr_pos _ := by omega
     fr_le x := by have := Nat.le_mul_self x.n; omega
     vals x σ hn hU _ := by simp [s3Task, threeSumInst, hn, hU]
     safe x lim σ hn _ _ hw := by
       have : (x.n : ℤ) ≤ (x.n : ℤ) * x.n := by exact_mod_cast Nat.le_mul_self x.n
       push_cast at hw; simp [hn, abs_le]; omega
     zero x hn _ := ⟨⟨fun h => absurd h (by simp), fun ⟨i, _⟩ => absurd i.isLt (by omega)⟩, trivial⟩
     pre x hn hU :=
       { N_pos := hn, U_pos := hU, len := List.length_ofFn
         seg := by simpa [EndStatement.ThreeSum, threeSumInst] using seg_memOf [(x.n : ℤ)] (List.ofFn x.x) []
         le := fun _ ha => Bounded.abs_le ha
         below := (Nat.add_comm 1 x.n).le }
     post x r μ' _ h := by
       obtain ⟨rfl, -⟩ := h
       exact ⟨(verdictOf_flag _).trans (iff_of_eq (congrArg ThreeSum (vecOf_ofFn x.x))), trivial⟩
     : Wrap EndStatement.ThreeSum s3Task true }).realized h

theorem triOf_rowMajor {n : ℕ} (T : TriangleInstance ℤ n) :
    triOf n (rowMajor T.wAB) (rowMajor T.wBC) (rowMajor T.wAC) = T := by
  cases T with
  | mk wAB wBC wAC =>
    unfold triOf
    congr 1 <;> funext i j <;> exact getD_rowMajor _ i j

def triangleInst (x : Bounded EndStatement.ExactTriangle) : etTask.Inst :=
  ⟨x.n, x.U, 1, 1 + x.n * x.n, 1 + 2 * (x.n * x.n), rowMajor x.x.1, rowMajor x.x.2.1,
    rowMajor x.x.2.2⟩

theorem realized_exactTriangle (T : ℕ → ℝ → ℝ) (h : SolvedIn etTask T) :
    Realized EndStatement.ExactTriangle T :=
  ({ args := [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3, k 1 +' k 3 *' v 3]
     inst := triangleInst
     fr x := 1 + 3 * (x.n * x.n)
     size_eq _ := rfl
     bound_eq _ := rfl
     fr_pos _ := by omega
     fr_le _ := by omega
     vals x σ hn hU hnn := by simp [etTask, triangleInst, hn, hU, hnn]
     safe x lim σ _ _ hnn hw := safe_fourAddresses (by omega) hnn hw
     zero x hn _ := ⟨⟨fun h => absurd h (by simp), fun ⟨a, _⟩ => absurd a.isLt (by omega)⟩, trivial⟩
     pre x hn hU := by
       have hAB : (rowMajor x.x.1).length = x.n * x.n := length_rowMajor _
       have hBC : (rowMajor x.x.2.1).length = x.n * x.n := length_rowMajor _
       have hin : (ofEnd EndStatement.ExactTriangle).input x =
           (x.n : ℤ) :: (rowMajor x.x.1 ++ rowMajor x.x.2.1 ++ rowMajor x.x.2.2) := by
         simp only [EndStatement.ExactTriangle, rowByRow_eq]
       have hb : ∀ {a : ℤ}, a ∈ rowMajor x.x.1 ++ rowMajor x.x.2.1 ++ rowMajor x.x.2.2 → |a| ≤ (x.U : ℤ) :=
         fun ha => Bounded.abs_le (by simpa only [EndStatement.ExactTriangle, rowByRow_eq] using ha)
       rw [hin]
       exact triPre_of_arrays (base := 1) hn hU
         { len := hAB
           seg := by
             have := seg_first (x.n : ℤ) (rowMajor x.x.1) (rowMajor x.x.2.1 ++ rowMajor x.x.2.2)
             rwa [← List.append_assoc] at this
           bound := fun _ (ha : _ ∈ rowMajor x.x.1) => hb (by simp [ha]) }
         { len := hBC
           seg := by
             have := seg_memOf ((x.n : ℤ) :: rowMajor x.x.1) (rowMajor x.x.2.1) (rowMajor x.x.2.2)
             rwa [List.length_cons, hAB, Nat.add_comm] at this
           bound := fun _ (ha : _ ∈ rowMajor x.x.2.1) => hb (by simp [ha]) }
         { len := length_rowMajor _
           seg := by
             have := seg_second (x.n : ℤ) (rowMajor x.x.1 ++ rowMajor x.x.2.1) (rowMajor x.x.2.2)
             rwa [List.length_append, hAB, hBC, ← Nat.two_mul] at this
           bound := fun _ (ha : _ ∈ rowMajor x.x.2.2) => hb (by simp [ha]) }
     post x r μ' _ h := by
       obtain ⟨rfl, -⟩ := h
       exact ⟨(verdictOf_flag _).trans (iff_of_eq (congrArg TriangleInstance.HasZeroTriangle
         (triOf_rowMajor ⟨x.x.1, x.x.2.1, x.x.2.2⟩))), trivial⟩
     : Wrap EndStatement.ExactTriangle etTask true }).realized h

def minPlusInst (x : Bounded EndStatement.MinPlusProduct) : mpTask.Inst :=
  ⟨x.n, x.U, 1, 1 + x.n * x.n, 1 + 2 * (x.n * x.n), rowMajor x.x.1, rowMajor x.x.2⟩

theorem realized_minPlusProduct (T : ℕ → ℝ → ℝ) (h : SolvedIn mpTask T) :
    Realized EndStatement.MinPlusProduct T :=
  ({ args := [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3, k 1 +' k 3 *' v 3]
     inst := minPlusInst
     fr x := 1 + 3 * (x.n * x.n)
     size_eq _ := rfl
     bound_eq _ := rfl
     fr_pos _ := by omega
     fr_le _ := by omega
     vals x σ hn hU hnn := by simp [mpTask, minPlusInst, hn, hU, hnn]
     safe x lim σ _ _ hnn hw := safe_fourAddresses (by omega) hnn hw
     zero x hn _ := ⟨⟨fun _ => trivial, fun _ => rfl⟩, fun i => absurd i.isLt (by omega)⟩
     pre x hn hU := by
       have hA : (rowMajor x.x.1).length = x.n * x.n := length_rowMajor _
       have hin : (ofEnd EndStatement.MinPlusProduct).input x =
           (x.n : ℤ) :: (rowMajor x.x.1 ++ rowMajor x.x.2) := by
         simp only [EndStatement.MinPlusProduct, rowByRow_eq]
       have hb : ∀ {a : ℤ}, a ∈ rowMajor x.x.1 ++ rowMajor x.x.2 → |a| ≤ (x.U : ℤ) :=
         fun ha => Bounded.abs_le (by simpa only [EndStatement.MinPlusProduct, rowByRow_eq] using ha)
       rw [hin]
       exact
         { n_pos := hn, U_pos := hU, lenA := hA, lenB := length_rowMajor _
           segA := seg_first _ _ _
           segB := by have := seg_second (x.n : ℤ) (rowMajor x.x.1) (rowMajor x.x.2); rwa [hA] at this
           leA := fun _ (ha : _ ∈ rowMajor x.x.1) => hb (by simp [ha])
           leB := fun _ (ha : _ ∈ rowMajor x.x.2) => hb (by simp [ha])
           belowA := by simp [minPlusInst]; omega
           belowB := by simp [minPlusInst]; omega
           belowC := by simp [minPlusInst]; omega
           apartA := Or.inl (by simp [minPlusInst]; omega)
           apartB := Or.inl (by simp [minPlusInst]; omega) }
     post x r μ' hn h := by
       have hseg : Seg μ' (1 + 2 * (x.n * x.n)) (minPlusList x.n (rowMajor x.x.1) (rowMajor x.x.2)) := h.1
       have hlen : ((ofEnd EndStatement.MinPlusProduct).input x).length = 1 + 2 * (x.n * x.n) := by
         simp only [EndStatement.MinPlusProduct, rowByRow_eq, List.length_cons, List.length_append,
           length_rowMajor]
         omega
       refine ⟨by simp [verdictOf, EndStatement.MinPlusProduct], fun i j => ?_⟩
       have hcell : μ' (((ofEnd EndStatement.MinPlusProduct).input x).length +
           ((i : ℕ) * x.n + (j : ℕ))) = minPlusEntry x.n (rowMajor x.x.1) (rowMajor x.x.2) i j := by
         rw [hlen, hseg.getD (by rw [length_minPlusList]; exact Nat.mul_add_lt_mul i.isLt j.isLt) 0]
         exact entry_minPlusList _ _ i.isLt j.isLt
       obtain ⟨l, hl, hmin⟩ := exists_minPlusEntry_eq hn (rowMajor x.x.1) (rowMajor x.x.2) i j
       refine ⟨⟨⟨l, hl⟩, hcell.trans ?_⟩, fun l' => hcell.le.trans ?_⟩
       · rw [hmin, entry, entry, getD_rowMajor x.x.1 i ⟨l, hl⟩, getD_rowMajor x.x.2 ⟨l, hl⟩ j]
       · have := minPlusEntry_le x.n (rowMajor x.x.1) (rowMajor x.x.2) i j l'.isLt
         rwa [entry, entry, getD_rowMajor x.x.1 i l', getD_rowMajor x.x.2 l' j] at this
     : Wrap EndStatement.MinPlusProduct mpTask false }).realized h

def apspAdj (x : Bounded EndStatement.APSP) : List ℤ :=
  rowMajor fun i j => if (x.x.1 i j).isSome then 1 else 0

def apspWeights (x : Bounded EndStatement.APSP) : List ℤ := rowMajor fun i j => (x.x.1 i j).getD 0

theorem input_apsp (x : Bounded EndStatement.APSP) :
    (ofEnd EndStatement.APSP).input x = (x.n : ℤ) :: (apspAdj x ++ apspWeights x) := by
  simp only [EndStatement.APSP, rowByRow_eq, apspAdj, apspWeights]

theorem graphOf_apsp (x : Bounded EndStatement.APSP) :
    graphOf x.n (apspAdj x) (apspWeights x) = fun i j => toTop (x.x.1 i j) := by
  funext i j
  unfold graphOf apspAdj apspWeights
  rw [getD_rowMajor _ i j, getD_rowMajor _ i j]
  cases x.x.1 i j <;> simp [toTop]

def apspInst (x : Bounded EndStatement.APSP) : GraphInst :=
  ⟨x.n, x.U, 1, 1 + x.n * x.n, 1 + 2 * (x.n * x.n), apspAdj x, apspWeights x⟩

theorem realized_apsp (T : ℕ → ℝ → ℝ) (h : SolvedIn apTask T) :
    Realized EndStatement.APSP T :=
  ({ args := [v 1, v 2, k 1, k 1 +' v 3, k 1 +' k 2 *' v 3, k 1 +' k 4 *' v 3]
     inst := apspInst
     fr x := 1 + 4 * (x.n * x.n)
     size_eq _ := rfl
     bound_eq _ := rfl
     fr_pos _ := by omega
     fr_le _ := by omega
     vals x σ hn hU hnn := by simp [apTask, apspInst, hn, hU, hnn]
     safe x lim σ _ _ hnn hw := safe_fourAddresses (by omega) hnn hw
     zero x hn _ := ⟨⟨fun _ => trivial, fun _ => rfl⟩, fun i => absurd i.isLt (by omega)⟩
     pre x hn hU := by
       have hA : (apspAdj x).length = x.n * x.n := length_rowMajor _
       rw [input_apsp]
       exact
         { n_pos := hn, U_pos := hU, lenADJ := hA, lenW := length_rowMajor _
           segADJ := seg_first _ _ _
           segW := by have := seg_second (x.n : ℤ) (apspAdj x) (apspWeights x); rwa [hA] at this
           leW := fun a (ha : a ∈ apspWeights x) => Bounded.abs_le (by
             simpa only [EndStatement.APSP, rowByRow_eq, apspAdj, apspWeights] using
               List.mem_append_right (apspAdj x) ha)
           belowADJ := by simp [apspInst]; omega
           belowW := by simp [apspInst]; omega
           belowOut := by simp [apspInst]; omega
           noNegativeCycle :=
             (congrArg NoNegativeCycle (graphOf_apsp x)).mpr (noNegativeCycle_toTop x.x.2) }
     post x r μ' _ h := by
       obtain ⟨⟨dist, hdist, hcells⟩, -⟩ := h
       have hdist' : IsDistanceMatrix (fun i j => toTop (x.x.1 i j)) dist :=
         (congrArg (fun w => IsDistanceMatrix w dist) (graphOf_apsp x)).mp hdist
       have hlen : ((ofEnd EndStatement.APSP).input x).length = 1 + 2 * (x.n * x.n) := by
         have hA : (apspAdj x).length = x.n * x.n := length_rowMajor _
         have hB : (apspWeights x).length = x.n * x.n := length_rowMajor _
         rw [input_apsp, List.length_cons, List.length_append, hA, hB]; omega
       refine ⟨by simp [verdictOf, EndStatement.APSP], output_apsp x.x _ fun i j => ?_⟩
       rw [hlen]
       exact reachable_or_not hdist' (hcells i j).1 (hcells i j).2
     : Wrap EndStatement.APSP apTask false }).realized h

theorem claim_theorem_21a : Claim.Theorem_21a lightModel :=
  Theorem21a.of_CH20_VW13 _ ChanHe.claim_CH20_Theorem_5_1 claim_VW13_Theorem_4_3

theorem threeSum_of_uniform {δ : ℝ} {e : ℕ} (hδ : δ ≤ 1)
    (hu : Claim.ExactTriangleUniform lightModel δ e) {r : ℚ} (hr0 : 0 ≤ r) (ha : 2 - δ / 2 < r) :
    EndStatement.ThreeSum.SolvedInTime r :=
  FromClaims.solvedInTime_of_claim realized_threeSum hr0
    (threeSum_of_uniform_theorem_21a _ e hδ hu claim_theorem_21a ha)

end Light.Sec3
