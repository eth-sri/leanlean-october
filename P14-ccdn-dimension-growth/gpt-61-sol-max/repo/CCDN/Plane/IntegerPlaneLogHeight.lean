/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Plane.IntegerPlaneHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CCDN.ForMathlib.Log

/-! The bounded-parameter section loses only O_m(d²) in logarithmic height.
The resulting nonzero integer witness fits the fourth-power prime cutoff. -/

@[expose] public section
namespace CCDN
open MvPolynomial

variable (m d : ℕ) (hd : 1 ≤ d) (H : ℝ) (hH : 1 ≤ H)

include hd hH in
/-- For `d ≥ 1` and `H ≥ 1`, the interpolation height `integerPlaneHeight m d H (2 * d ^ 3)` is at
least `1`. -/
lemma integerPlaneHeight_one_le  :
    1 ≤ integerPlaneHeight m d H (2 * ↑d ^ 3) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply one_le_mul_of_one_le_of_one_le
  · simp_all [one_le_pow₀]
  · grind [one_le_mul_of_one_le_of_one_le, one_le_pow₀]

include hd hH in
private lemma integerPlaneHeight_log_le  :
    Real.log (integerPlaneHeight m d H (2 * ↑d ^ 3)) ≤
      Real.log H + ↑m * d + 11 * ↑d ^ 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hH0 : 0 < H := by linarith
  have hl1 : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self hd0.le
  have hl2 : Real.log (1 + 2 * ↑d) ≤ 2 * d := by
    grind [add_comm, Real.log_add_one_le_self]
  have hld := Real.log_le_self hd0.le
  have hltwo := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)
  have hA : Real.log (2 * ↑d ^ 3 * (1 + 2 * d)) ≤ 7 * d := by
    grind [Real.log_mul, Real.log_pow]
  unfold integerPlaneHeight
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hH0.ne', Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  calc
    _ ≤ (2 * (↑d + 1)) * d + (↑m * d + Real.log H + d * (7 * d)) := by
      gcongr
    _ ≤ _ := by nlinarith

/-- A dimension-dependent constant at the d⁴ cutoff. -/
noncomputable def hypersurfaceHeightConstant (m : ℕ) : ℝ := 28 * (m + 12)

/-- The constant `hypersurfaceHeightConstant m` is at least `1`. -/
lemma hypersurfaceHeightConstant_one_le (m : ℕ) : 1 ≤ hypersurfaceHeightConstant m := by
  unfold hypersurfaceHeightConstant
  linarith

include hd hH in
/-- For `d ≥ 1` and `H ≥ 1`, with `L` the logarithm of the interpolation height
`integerPlaneHeight m d H (2 * d ^ 3)`, the quantity `L + 27 d⁴ (1 + L / d²)` is at most
`27 d⁴ · hypersurfaceHeightConstant m · (1 + log H / d²)`. -/
lemma integerPlaneHeight_scaled_log_le  :
    Real.log (integerPlaneHeight m d H (2 * ↑d ^ 3)) +
        (27 * ↑d ^ 4) *
          (1 + Real.log (integerPlaneHeight m d H (2 * ↑d ^ 3)) / ↑d ^ 2) ≤
      (27 * ↑d ^ 4) *
        (hypersurfaceHeightConstant m * (1 + Real.log H / ↑d ^ 2)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog := Real.log_nonneg hH
  have hc := integerPlaneHeight_log_le m d hd H hH
  have hd2 : ↑d ^ 2 ≤ (d : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
  have hd3 : ↑d ^ 3 ≤ (d : ℝ) ^ 4 := by
    nlinarith
  have hd12 : ↑d ≤ (d : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ 1 + 27 * ↑d ^ 2 by positivity)
  have hmid : (1 + 27 * ↑d ^ 2) *
      (Real.log H + ↑m * d + 11 * ↑d ^ 2) + 27 * ↑d ^ 4 ≤
      28 * ↑d ^ 2 * Real.log H + hypersurfaceHeightConstant m * ↑d ^ 4 := by
    unfold hypersurfaceHeightConstant
    nlinarith
  have hconst : 28 ≤ hypersurfaceHeightConstant m := by
    unfold hypersurfaceHeightConstant
    linarith
  have hlast : 28 * ↑d ^ 2 * Real.log H + hypersurfaceHeightConstant m * ↑d ^ 4 ≤
      27 * hypersurfaceHeightConstant m * ↑d ^ 4 +
        27 * hypersurfaceHeightConstant m * ↑d ^ 2 * Real.log H := by
    have h1 := mul_le_mul_of_nonneg_right hconst (mul_nonneg (sq_nonneg ↑d) hlog)
    nlinarith
  have he (S : ℝ) : S + 27 * ↑d ^ 4 * (1 + S / ↑d ^ 2) =
      (1 + 27 * ↑d ^ 2) * S + 27 * ↑d ^ 4 := by
    field_simp
    ring
  rw [he]
  have hr : 27 * ↑d ^ 4 *
      (hypersurfaceHeightConstant m * (1 + Real.log H / ↑d ^ 2)) =
      27 * hypersurfaceHeightConstant m * ↑d ^ 4 +
        27 * hypersurfaceHeightConstant m * ↑d ^ 2 * Real.log H := by field_simp
  rw [hr]
  exact (add_le_add hmul le_rfl).trans (hmid.trans hlast)

end CCDN
