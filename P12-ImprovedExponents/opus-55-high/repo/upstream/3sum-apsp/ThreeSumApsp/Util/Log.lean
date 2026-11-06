/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Logarithms and real powers

Small facts on `Real.log`, `Real.logb`, `Nat.clog`, `Real.sqrt` and real powers that the estimates
of the paper use silently.

* Values, in the namespace `Real` and named by Mathlib's convention: `1 / 2 < log 2 < 1`,
  `log 4 = 2 log 2`, `log 9 = 2 log 3`, `1 ≤ log 4`, `1 / 2 ≤ log x` for `x ≥ 2`, `1 ≤ log x` for
  `x ≥ 3`, `log₂ 7 < 2.81`, `4 ≤ √D` for `D ≥ 16`.
* The rounded logarithm: `⌈log_b n⌉ < log_b n + 1` (`Real.natCast_clog_lt_logb_add_one`),
  `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)` (`Real.pow_clog_le_mul_rpow_logb`).
* The definition `logU u = log (max u 2)`, the paper's `log U`.
-/


namespace Real

/-! ### Values -/

/-- `1 / 2 < log 2`. -/
theorem one_half_lt_log_two : 1 / 2 < log 2 :=
  lt_trans (by norm_num) log_two_gt_d9

/-- `log 2 < 1`. -/
theorem log_two_lt_one : log 2 < 1 :=
  log_two_lt_d9.trans (by norm_num)

/-- `log 4 = 2 log 2`. -/
theorem log_four : log 4 = 2 * log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]

/-- `log 9 = 2 log 3`. -/
theorem log_nine : log 9 = 2 * log 3 := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow, Nat.cast_ofNat]

/-- `1 ≤ log 4`. -/
theorem one_le_log_four : 1 ≤ log 4 := by
  linarith [log_four, one_half_lt_log_two]

variable {x : ℝ}

/-- `1 ≤ log x` for `x ≥ 3`. -/
theorem one_le_log_of_three_le (hx : 3 ≤ x := by linarith) : 1 ≤ log x :=
  by grind [le_log_iff_exp_le, exp_one_lt_three]

variable {n : ℕ}

/-- `1 ≤ log n` for a natural number `n ≥ 3`. -/
theorem one_le_log_natCast_of_three_le (hn : 3 ≤ n) : 1 ≤ log n :=
  one_le_log_of_three_le (by simp_all)

/-- `1 / 2 ≤ log x` for `x ≥ 2`. -/
theorem one_half_le_log_of_two_le (hx : 2 ≤ x := by simp_all) : 1 / 2 ≤ log x :=
  one_half_lt_log_two.le.trans (log_le_log two_pos hx)

/-- `4 ≤ √D` for a natural number `D ≥ 16`. -/
theorem four_le_sqrt_natCast_of_sixteen_le {D : ℕ} (hD : 16 ≤ D) : 4 ≤ √(D : ℝ) :=
  le_sqrt_of_sq_le (by norm_num; assumption)

/-! ### The rounded logarithm `Nat.clog` -/

/-- `⌈log_b n⌉ < log_b n + 1`, for all natural numbers `b` and `n` (for `b ≤ 1` or `n = 0` both
logarithms are `0`). -/
theorem natCast_clog_lt_logb_add_one (b n : ℕ) : (Nat.clog b n : ℝ) < logb b n + 1 := by
  rw [← natCeil_logb_natCast]
  exact Nat.ceil_lt_add_one (div_nonneg (log_natCast_nonneg n) (log_natCast_nonneg b))

/-- `c ^ ⌈log_b n⌉ ≤ c * n ^ (log_b c)`, for natural numbers `b` and `n ≥ 1` and a real number
`c ≥ 1`. -/
theorem pow_clog_le_mul_rpow_logb (b : ℕ) {c : ℝ} (hn : 1 ≤ n) (hc : 1 ≤ c) :
    c ^ Nat.clog b n ≤ c * (n : ℝ) ^ logb b c := by
  have hswap : c ^ logb b n = n ^ logb b c := by
    grind [rpow_def_of_pos, Nat.cast_pos, logb]
  calc c ^ b.clog n = c ^ (Nat.clog b n : ℝ) := by simp
    _ ≤ c ^ (logb b n + 1) :=
        by grind [rpow_le_rpow_of_exponent_le, natCast_clog_lt_logb_add_one]
    _ = c * n ^ logb b c := by grind [rpow_add_one, mul_comm]

end Real

namespace ThreeSumApsp

/-- `log U`, read as `log 2` for `U < 2`, so that a bound with `log U` is positive at `U = 1` as
well. It occurs in the bounds of Theorem 21(b) and in the overhead for copying in
`ConditionalTimes.Claim.RectMinPlusFromSquare`. -/
noncomputable def logU (u : ℝ) : ℝ := Real.log (max u 2)
