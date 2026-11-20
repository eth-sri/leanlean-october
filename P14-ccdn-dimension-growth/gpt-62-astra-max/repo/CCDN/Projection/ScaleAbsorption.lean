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
noncomputable section

variable (n : ℕ) {d : ℕ} (hd : 0 < d)

/-- The constant `c = (n+1 : ℝ) * birationalProjectionHeightConstant n + 2*n`, for which `log (projectionBoxFactor n d) ≤ c * d`. -/
def projectionLogConstant : ℝ := (n+1 : ℝ) * birationalProjectionHeightConstant n + 2*n

/-- The projection log constant is nonnegative. -/
lemma projectionLogConstant_nonneg : 0 ≤ projectionLogConstant n := by
  unfold projectionLogConstant
  positivity

include hd in
/-- For `d > 0`, the logarithm of the projection box factor is at most
`projectionLogConstant n * d`. -/
lemma projectionBoxFactor_log_le :
    Real.log (projectionBoxFactor n d) ≤ projectionLogConstant n * d := by
  have hC : (0 : ℝ) < (n+1 : ℝ) * birationalProjectionHeightConstant n := by
    have := birationalProjectionHeightConstant_pos n
    positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold projectionBoxFactor projectionLogConstant
  rw [Real.log_mul hC.ne' (by positivity), Real.log_pow]
  push_cast
  have := Real.log_le_self hC.le
  have := Real.log_add_one_le_self (Nat.cast_nonneg (α := ℝ) d)
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr (Real.log_add_one_le_self (Nat.cast_nonneg (α := ℝ) d))), mul_nonneg hC.le (sub_nonneg.mpr hd1)]

include hd in
private lemma curveBound_scale_of_log_le {A B C : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hlog : Real.log A ≤ C * d) :
    curveBound d (A * B) ≤ Real.exp C * (C + 1) * curveBound d B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hlogB := Real.log_nonneg hB
  have hlogA := Real.log_nonneg hA
  have hpow : A ^ (1 / (d : ℝ)) ≤ Real.exp C := by
    rw [Real.rpow_def_of_pos hA0, Real.exp_le_exp, ← div_eq_mul_one_div]
    exact (div_le_iff₀ hd0).mpr hlog
  have hlog₂ : Real.log A + Real.log B + d ≤ (C + 1) * (Real.log B + d) := by
    nlinarith [mul_nonneg hC hlogB]
  unfold curveBound
  rw [Real.mul_rpow hA0.le hB0.le, Real.log_mul hA0.ne' hB0.ne']
  calc
    _ ≤ (d : ℝ) ^ 3 * (Real.exp C * B ^ (1 / (d : ℝ))) *
        ((C + 1) * (Real.log B + d)) := by gcongr
    _ = _ := by ring

include hd in
/-- Scaling the radius by the projection box factor multiplies the curve bound by at most a
constant depending only on `n`: with `c = projectionLogConstant n`, for `d > 0` and `B ≥ 1`,
`curveBound d (projectionBoxFactor n d * B) ≤ exp c * (c + 1) * curveBound d B`. -/
theorem projection_curveBound_scale
    {B : ℝ} (hB : 1 ≤ B) :
    curveBound d (projectionBoxFactor n d * B) ≤
      (Real.exp (projectionLogConstant n) * (projectionLogConstant n + 1)) * curveBound d B :=
  by grind [curveBound_scale_of_log_le, projectionBoxFactor_one_le, projectionLogConstant_nonneg, projectionBoxFactor_log_le]

end
end CCDN
