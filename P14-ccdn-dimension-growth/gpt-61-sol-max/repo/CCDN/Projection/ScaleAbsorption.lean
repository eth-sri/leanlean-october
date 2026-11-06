/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.DegreePreservingProjectionBox
public import CCDN.Statements
import CCDN.ForMathlib.Log

/-! Absorb the degree-dependent projection box factor into a constant depending
only on ambient dimension, retaining the exact exponent 1/d and d³ factor. -/

@[expose] public section
namespace CCDN

/-- The constant `c = 2 * n ^ 2 + 3 * n`, for which `log (projectionBoxFactor n d) ≤ c * d`. -/
noncomputable def projectionLogConstant (n : ℕ) : ℝ := 2 * ↑n ^ 2 + 3 * n

/-- The projection log constant is nonnegative. -/
lemma projectionLogConstant_nonneg (n : ℕ) : 0 ≤ projectionLogConstant n := by
  unfold projectionLogConstant
  positivity

variable (n : ℕ) {d : ℕ} (hd : 0 < d)

include hd in
/-- For `d > 0`, the logarithm of the projection box factor is at most
`projectionLogConstant n * d`. -/
lemma projectionBoxFactor_log_le  :
    Real.log (projectionBoxFactor n d) ≤ projectionLogConstant n * d := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hd0 : (0 : ℝ) < d + 1 := by positivity
  have hln := Real.log_add_one_le_self hn
  have hld := Real.log_add_one_le_self d.cast_nonneg
  unfold projectionBoxFactor
  rw [Real.log_mul hn0.ne' (pow_pos (pow_pos (mul_pos hn0 hd0) _) _).ne',
    Real.log_pow, Real.log_pow, Real.log_mul hn0.ne' hd0.ne']
  unfold projectionLogConstant
  norm_num only [Nat.cast_ofNat]
  nlinarith


include hd in
/-- Scaling the radius by the projection box factor multiplies the curve bound by at most a
constant depending only on `n`: with `c = projectionLogConstant n`, for `d > 0` and `B ≥ 1`,
`curveBound d (projectionBoxFactor n d * B) ≤ exp c * (c + 1) * curveBound d B`. -/
theorem projection_curveBound_scale 
    {B : ℝ} (hB : 1 ≤ B) :
    curveBound d (projectionBoxFactor n d * B) ≤
      (Real.exp (projectionLogConstant n) * (projectionLogConstant n + 1)) * curveBound d B :=
  (by
    let inline_A := projectionBoxFactor n d
    let inline_C := projectionLogConstant n
    let inline_hA := projectionBoxFactor_one_le n d
    let inline_hC := projectionLogConstant_nonneg n
    let inline_hlog := projectionBoxFactor_log_le n hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
    have hA0 : 0 < inline_A := by linarith
    have hB0 : 0 < B := by linarith
    have hlogB := Real.log_nonneg hB
    have hlogA := Real.log_nonneg inline_hA
    have hpow : inline_A ^ (1 / (d : ℝ)) ≤ Real.exp inline_C := by
      rw [Real.rpow_def_of_pos hA0, Real.exp_le_exp, ← div_eq_mul_one_div]
      exact (div_le_iff₀ hd0).mpr inline_hlog
    have hlog₂ : Real.log inline_A + Real.log B + d ≤ (inline_C + 1) * (Real.log B + d) := by
      nlinarith [mul_nonneg inline_hC hlogB]
    unfold curveBound
    rw [Real.mul_rpow hA0.le hB0.le, Real.log_mul hA0.ne' hB0.ne']
    calc
      _ ≤ ↑d ^ 3 * (Real.exp inline_C * B ^ (1 / (d : ℝ))) *
          ((inline_C + 1) * (Real.log B + d)) := by gcongr
      _ = _ := by ring)

end CCDN
