/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Log

/-!
# Logarithms up to a constant factor

Bounds on logarithms in the calculus `Dominated`, for every argument of a domain and not only for
large ones.

* Absorbing logarithms, for `x ≥ 1`: `(log x + 1) ^ e` is `O(x ^ η)` for `η > 0`
  (`dominated_log_add_one_pow_rpow`), hence `x ^ a * (log x) ^ e = O(x ^ b)` for `a < b`
  (`dominated_rpow_mul_log_pow_rpow`).
* From 2 on: `log x + 1 = O(log x)` (`dominated_log_add_one_log`) and `⌈log_b n⌉ + 1 = O(log n)`
  (`dominated_clog_add_one_log`).

For a natural number or a field of a parameter record in place of `x`, use `Dominated.comp`.
-/

public section

namespace ThreeSumApsp

open Real

/-! ### Absorbing logarithms, for all `x ≥ 1` -/

/-! ### `log x + 1` and `⌈log_b n⌉ + 1` are `O(log)`, from `2` on -/

/-- `log x + 1 = O(log x)` on `x ≥ 2`. -/
theorem dominated_log_add_one_log :
    Dominated (fun x : ℝ => 2 ≤ x) (fun x => log x + 1) fun x => log x :=
  .of_le_const_mul (C := 3) (by norm_num) fun _ hx => by
    linarith [one_half_le_log_of_two_le hx]

/-- `⌈log_b n⌉ + 1 = O(log n)` on `n ≥ 2`, for every natural number `b`. -/
theorem dominated_clog_add_one_log (b : ℕ) :
    Dominated (fun n : ℕ => 2 ≤ n) (fun n => (Nat.clog b n : ℝ) + 1) fun n => log n := by
  have hlogb : 0 ≤ log b := log_natCast_nonneg b
  refine .of_le_const_mul (C := 1 / log b + 4) (by positivity) fun n hn => ?_
  have hhalf : 1 / 2 ≤ log n := one_half_le_log_of_two_le (by exact_mod_cast hn)
  have hclog := natCast_clog_lt_logb_add_one b n
  rw [add_mul, one_div_mul_eq_div]
  -- `⌈log_b n⌉ + 1 < log n / log b + 2` and `2 ≤ 4 log n`
  rw [logb] at hclog
  linarith [hclog, hhalf]

end ThreeSumApsp
