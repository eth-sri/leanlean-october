/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.IntegerPlaneHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CCDN.ForMathlib.Log

/-! The bounded-parameter section loses only O_m(d²) in logarithmic height.
The resulting nonzero integer witness fits the fourth-power prime cutoff. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable (m d : ℕ) (hd : 1 ≤ d)
  (H : ℝ) (hH : 1 ≤ H)
include m d hd H hH

/-- For `d ≥ 1` and `H ≥ 1`, the interpolation height `integerPlaneHeight m d H (2 * d ^ 3)` is at
least `1`. -/
lemma integerPlaneHeight_one_le :
    1 ≤ integerPlaneHeight m d H (2 * (d : ℝ) ^ 3) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hA : 1 ≤ 2 * (d : ℝ) ^ 3 := by nlinarith [one_le_pow₀ hdR (n := 3)]
  unfold integerPlaneHeight
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ (by linarith)
  · apply one_le_mul_of_one_le_of_one_le
    · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hH
    · exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le hA (by linarith))

private lemma integerPlaneHeight_log_le :
    Real.log (integerPlaneHeight m d H (2 * (d : ℝ) ^ 3)) ≤
      Real.log H + (m : ℝ) * d + 11 * (d : ℝ) ^ 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hH0 : 0 < H := by linarith
  have hl1 : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self hd0.le
  have hl2 : Real.log (1 + 2 * (d : ℝ)) ≤ 2 * d := by
    rw [add_comm]
    exact Real.log_add_one_le_self (by positivity)
  have hld := Real.log_le_self hd0.le
  have hltwo := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)
  have hA : Real.log (2 * (d : ℝ) ^ 3 * (1 + 2 * d)) ≤ 7 * d := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
    linarith
  unfold integerPlaneHeight
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hH0.ne', Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  calc
    _ ≤ (2 * ((d : ℝ) + 1)) * d + ((m : ℝ) * d + Real.log H + d * (7 * d)) := by
      gcongr
    _ ≤ _ := by nlinarith

end

/-- A dimension-dependent constant at the d⁴ cutoff. -/
def hypersurfaceHeightConstant (m : ℕ) : ℝ := 28 * (m + 12)

/-- The constant `hypersurfaceHeightConstant m` is at least `1`. -/
lemma hypersurfaceHeightConstant_one_le (m : ℕ) : 1 ≤ hypersurfaceHeightConstant m := by
  unfold hypersurfaceHeightConstant
  linarith

/-- For `d ≥ 1` and `H ≥ 1`, with `L` the logarithm of the interpolation height
`integerPlaneHeight m d H (2 * d ^ 3)`, the quantity `L + 27 d⁴ (1 + L / d²)` is at most
`27 d⁴ · hypersurfaceHeightConstant m · (1 + log H / d²)`. -/
lemma integerPlaneHeight_scaled_log_le (m d : ℕ) (hd : 1 ≤ d)
    (H : ℝ) (hH : 1 ≤ H) :
    Real.log (integerPlaneHeight m d H (2 * (d : ℝ) ^ 3)) +
        (27 * (d : ℝ) ^ 4) *
          (1 + Real.log (integerPlaneHeight m d H (2 * (d : ℝ) ^ 3)) / (d : ℝ) ^ 2) ≤
      (27 * (d : ℝ) ^ 4) *
        (hypersurfaceHeightConstant m * (1 + Real.log H / (d : ℝ) ^ 2)) := by
  let L := Real.log (integerPlaneHeight m d H (2 * (d : ℝ) ^ 3))
  let D := (d : ℝ) ^ 2
  let P := 27 * (d : ℝ) ^ 4
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : 0 < D := by dsimp [D]; positivity
  have hDP : D ≤ P := by
    dsimp [D, P]
    nlinarith [pow_le_pow_right₀ hd1 (show 2 ≤ 4 by decide)]
  have hL : 0 ≤ L := Real.log_nonneg (integerPlaneHeight_one_le m d hd H hH)
  have hq : L / D ≤ Real.log H / D + (m : ℝ) + 11 := by
    apply (div_le_iff₀ hD).mpr
    have h := integerPlaneHeight_log_le m d hd H hH
    have hmd : (m : ℝ) * d ≤ m * D := by
      exact mul_le_mul_of_nonneg_left (by dsimp [D]; nlinarith) (by positivity)
    rw [add_mul, add_mul, div_mul_cancel₀ _ hD.ne']
    dsimp [D, L] at *
    linarith
  have ht := mul_le_mul_of_nonneg_right hDP (div_nonneg hL hD.le)
  rw [mul_div_cancel₀ _ hD.ne'] at ht
  change L + P * (1 + L / D) ≤ P * (hypersurfaceHeightConstant m * (1 + Real.log H / D))
  calc
    _ ≤ P * (1 + 2 * (L / D)) := by linarith
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (hD.le.trans hDP)
      unfold hypersurfaceHeightConstant
      nlinarith [div_nonneg (Real.log_nonneg hH) hD.le,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (div_nonneg (Real.log_nonneg hH) hD.le)]

end
end CCDN
