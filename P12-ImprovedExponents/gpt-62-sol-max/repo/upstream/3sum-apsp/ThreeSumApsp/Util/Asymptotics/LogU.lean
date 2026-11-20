/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Asymptotics.Dominated
public import ThreeSumApsp.Util.Log
public import ThreeSumApsp.Util.Asymptotics.PowPolylog

/-!
# `logU`, the paper's `log U`

`logU u` is `log u`, read as `log 2` for `u < 2`.

* It is positive and nondecreasing, and `log (cu) ≤ log c + log u` for `c ≥ 1`.
* `log (cU) = O(log U)` (`dominated_logU_mul`) and `log (c n^κ) = O(log n)`
  (`dominated_logU_mul_rpow`).
* Along bounds `u(n) ≤ c n^κ` it is `Õ(1)` (`isPowPolylog_logU_of_le`).
-/

public section

namespace ThreeSumApsp

/-- `logU u ≥ log 2`. -/
theorem log_two_le_logU (u : ℝ) : Real.log 2 ≤ logU u :=
  Real.log_le_log two_pos (le_max_right _ _)

/-- `logU u > 0`. -/
theorem logU_pos (u : ℝ) : 0 < logU u :=
  (Real.log_pos one_lt_two).trans_le (log_two_le_logU u)

/-- `1 + logU u ≥ 1`. -/
theorem one_le_one_add_logU (u : ℝ) : 1 ≤ 1 + logU u :=
  le_add_of_nonneg_right (logU_pos u).le

/-- `log u ≤ logU u` for `u > 0`. -/
theorem log_le_logU {u : ℝ} (hu : 0 < u) : Real.log u ≤ logU u :=
  Real.log_le_log hu (le_max_left _ _)

theorem log_mul_le_logU {a U : ℕ} (ha : a ≤ 4) (hU : 1 ≤ U) {u : ℝ} (hu : (U : ℝ) ≤ u) :
    (Nat.log 2 (a * U) : ℝ) ≤ 2 + 2 * logU u := by
  have hshift : Nat.log 2 (a * U) ≤ Nat.log 2 U + 2 := by
    have h := Nat.log_mono_right (b := 2) (Nat.mul_le_mul_right U ha)
    rw [show 4 * U = U * 2 * 2 by omega, Nat.log_mul_base (by decide) (by omega),
      Nat.log_mul_base (by decide) (by omega)] at h
    exact h
  have hpow : 2 ^ Nat.log 2 U ≤ U := Nat.pow_log_le_self 2 (by omega)
  have hpowR : (2 : ℝ) ^ Nat.log 2 U ≤ U := by exact_mod_cast hpow
  have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 U) ≤ logU u :=
    Real.log_le_log (by positivity) (hpowR.trans (hu.trans (le_max_left _ _)))
  rw [Real.log_pow] at hlog
  have h := mul_le_mul_of_nonneg_left Real.one_half_lt_log_two.le (Nat.cast_nonneg (Nat.log 2 U))
  have hs : (Nat.log 2 (a * U) : ℝ) ≤ ((Nat.log 2 U + 2 : ℕ) : ℝ) := Nat.cast_le.2 hshift
  push_cast at hs
  linarith

/-! ## `logU` of a multiple -/

/-! ## `logU` along bounds that are polynomial in `n` -/

/-- `log u(n) = Õ(1)` for bounds `1 ≤ u(n) ≤ c n^κ` on the numbers. -/
theorem isPowPolylog_logU_of_le {mag : ℕ → ℝ} {c κ : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → 1 ≤ mag n ∧ mag n ≤ c * (n : ℝ) ^ κ) :
    IsPowPolylog (fun n => logU (mag n)) 0 := by
  refine (isPowPolylog_log_mul_rpow (2 * c) κ).mono_left_of_nonneg
    (.of_forall fun n => (logU_pos _).le) ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  obtain ⟨hone, hle⟩ := h n hn
  refine Real.log_le_log (lt_max_of_lt_right two_pos) (max_le ?_ ?_) <;> rw [mul_assoc] <;> linarith

end ThreeSumApsp
