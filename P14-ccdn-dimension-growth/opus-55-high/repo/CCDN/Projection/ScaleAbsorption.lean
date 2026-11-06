/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Projection.DegreePreservingProjectionBox
import CCDN.Statements
import CCDN.ForMathlib.Log

/-! Absorb the degree-dependent projection box factor into a constant depending
only on ambient dimension, retaining the exact exponent 1/d and d³ factor. -/

namespace CCDN
section

section
variable (n : ℕ)

/-- The constant `c = 2 * n ^ 2 + 3 * n`, for which `log (projectionBoxFactor n d) ≤ c * d`. -/
def projectionLogConstant : ℝ := 2 * (n : ℝ) ^ 2 + 3 * n

/-- The projection log constant is nonnegative. -/
lemma projectionLogConstant_nonneg : 0 ≤ projectionLogConstant n := by
  unfold projectionLogConstant
  positivity

end

variable {d : ℕ}

/-- For `d > 0`, the logarithm of the projection box factor is at most
`projectionLogConstant n * d`. -/
lemma projectionBoxFactor_log_le (n : ℕ) (hd : 0 < d) :
    Real.log (projectionBoxFactor n d) ≤ projectionLogConstant n * d := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hd0 : (0 : ℝ) < d + 1 := by positivity
  have hln := Real.log_add_one_le_self hn
  have hld := Real.log_add_one_le_self d.cast_nonneg
  unfold projectionBoxFactor
  rw [Real.log_mul hn0.ne' (pow_pos (pow_pos (mul_pos hn0 hd0) _) _).ne',
    Real.log_pow, Real.log_pow, Real.log_mul hn0.ne' hd0.ne']
  unfold projectionLogConstant
  have hh := mul_le_mul_of_nonneg_left (add_le_add hln hld) (show 0 ≤ 2 * (n : ℝ) by positivity)
  have hh₂ := mul_le_mul_of_nonneg_left hd1 (show 0 ≤ 2 * (n : ℝ) ^ 2 + n by positivity)
  norm_num
  nlinarith

lemma curveBound_scale_of_log_le (hd : 0 < d) {A B C : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hlog : Real.log A ≤ C * d) :
    curveBound d (A * B) ≤ Real.exp C * (C + 1) * curveBound d B := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hlogB := Real.log_nonneg hB
  have hlogA := Real.log_nonneg hA
  have hpow : A ^ (1 / (d : ℝ)) ≤ Real.exp C := by
    rw [Real.rpow_def_of_pos hA0, Real.exp_le_exp, ← div_eq_mul_one_div]
    exact (div_le_iff₀ (mod_cast hd)).mpr hlog
  have hlog₂ : Real.log A + Real.log B + d ≤ (C + 1) * (Real.log B + d) := by
    nlinarith
  unfold curveBound
  rw [Real.mul_rpow hA0.le hB0.le, Real.log_mul hA0.ne' hB0.ne']
  calc
    _ ≤ (d : ℝ) ^ 3 * (Real.exp C * B ^ (1 / (d : ℝ))) *
        ((C + 1) * (Real.log B + d)) := by gcongr
    _ = _ := by ring

