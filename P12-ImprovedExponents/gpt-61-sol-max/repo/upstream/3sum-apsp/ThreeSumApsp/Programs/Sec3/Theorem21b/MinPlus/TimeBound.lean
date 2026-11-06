/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
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
public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic
public import ThreeSumApsp.Util.Asymptotics.LogU

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

@[expose] public section

/-! ## Good running times -/

namespace ThreeSumApsp.GoodTime

variable {T : ℕ → ℝ → ℝ}

end ThreeSumApsp.GoodTime

namespace Light.Sec3

open ThreeSumApsp

namespace MinPlusFromNeg

/-! ## The parameters of a bound -/

/-! ## Finding from deciding -/

/-! ## All pairs from finding -/

/-! ## The product from all pairs -/

/-- The number of rounds of the search is O(log u). -/
theorem mpRounds_le {U : ℕ} (hU : 1 ≤ U) {u} (hu : (U : ℝ) ≤ u) :
    (mpRounds U : ℝ) ≤ 8 * logU u := by
  have  : (1 : ℝ) ≤ U := mod_cast hU
  have  := Real.one_half_lt_log_two
  have hpow : 2 ^ Nat.log 2 (4 * U) ≤ 4 * U := Nat.pow_log_le_self 2 (by omega)
  -- ⌊log₂ 4U⌋ log 2 ≤ log 4U = 2 log 2 + log U
  have hlog : (Nat.log 2 (4 * U) : ℝ) * Real.log 2 ≤ Real.log (4 * U) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (mod_cast hpow)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_four] at hlog
  have  := (Real.log_le_log (by positivity) hu).trans
    (log_le_logU (by linarith))
  have  := log_two_le_logU u

  simp_all [mpRounds] <;> nlinarith

end MinPlusFromNeg

end Light.Sec3
