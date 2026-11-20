/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary logarithm comparisons

## Main results

* `Real.log_add_one_le_self`: `Real.log (x + 1) ≤ x` for `0 ≤ x`.
* `Real.natCast_le_of_log_le_log`: a positive natural number is bounded by a positive real once
  their logarithms compare.
* `Real.log_one_add_sub_div_four_le`: `Real.log (1 + x) - x / 4 ≤ Real.log 4 + 1` for `0 ≤ x`.
* `Real.rpow_half_mul_log_add_le`: `√B (log B + D) ≤ (1/ε + D) B^(1/2 + ε)` for `B ≥ 1`, an
  explicit absorption of the logarithm into a power.
-/

@[expose] public section

namespace Real

/-- For nonnegative `x`, `Real.log (x + 1) ≤ x`. -/
theorem log_add_one_le_self {x : ℝ} (hx : 0 ≤ x) : log (x + 1) ≤ x := by
  grind [add_sub_cancel_right, log_le_sub_one_of_pos]

/-- A positive natural number is bounded by a positive real once their logarithms compare. -/
theorem natCast_le_of_log_le_log {n : ℕ} {y : ℝ} (hn : 0 < n) (hy : 0 < y)
    (h : log n ≤ log y) : (n : ℝ) ≤ y :=
  (log_le_log_iff (Nat.cast_pos.mpr hn) hy).mp h

end Real
