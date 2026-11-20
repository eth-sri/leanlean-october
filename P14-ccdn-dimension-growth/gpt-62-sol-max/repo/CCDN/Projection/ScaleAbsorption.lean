/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.ProjectionHeight
import CCDN.Projection.BoundedBirationalHypersurfaceProjection
public import CCDN.Statements
import CCDN.ForMathlib.Log

/-! Absorb the degree-dependent projection box factor into a constant depending
only on ambient dimension, retaining the exact exponent 1/d and d³ factor. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The logarithm of the projection radius factor grows at most linearly with degree. -/
def projectionLogConstant (n : ℕ) : ℝ :=
  Real.log (((n : ℝ) + 1) * birationalProjectionHeightConstant n) + 2 * n

lemma projectionLogConstant_nonneg (n : ℕ) : 0 ≤ projectionLogConstant n := by
  have h : (1 : ℝ) ≤ birationalProjectionHeightConstant n := by
    exact_mod_cast Nat.succ_le_of_lt (birationalProjectionHeightConstant_pos n)
  exact add_nonneg (Real.log_nonneg (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (by positivity)) h)) (by positivity)

lemma projectionBoxFactor_log_le (n : ℕ) {d : ℕ} (hd : 0 < d) :
    Real.log (projectionBoxFactor n d) ≤ projectionLogConstant n * d := by
  have h : (1 : ℝ) ≤ birationalProjectionHeightConstant n := by
    exact_mod_cast Nat.succ_le_of_lt (birationalProjectionHeightConstant_pos n)
  have hA : (1 : ℝ) ≤ ((n : ℝ) + 1) * birationalProjectionHeightConstant n :=
    one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (by positivity)) h
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl : Real.log ((d : ℝ) + 1) ≤ d := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < d + 1)]
  unfold projectionBoxFactor projectionEntryBound projectionLogConstant
  rw [← mul_assoc, Real.log_mul (zero_lt_one.trans_le hA).ne' (by positivity), Real.log_pow]
  push_cast
  nlinarith [mul_nonneg (Real.log_nonneg hA) (sub_nonneg.mpr hd'),
    mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 2 * n)]

lemma projectionBoxFactor_rpow_le (n : ℕ) {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 ≤ r) :
    projectionBoxFactor n d ^ (r / (d : ℝ)) ≤ Real.exp (r * projectionLogConstant n) := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le (projectionBoxFactor_one_le n d)),
    Real.exp_le_exp, ← mul_div_assoc, mul_comm (Real.log _) r, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left ((div_le_iff₀ (by exact_mod_cast hd)).mpr (projectionBoxFactor_log_le n hd)) hr

/-- The enlarged box costs a constant depending only on the ambient dimension. -/
theorem projection_curveBound_scale (n : ℕ) {d : ℕ} (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    curveBound d (projectionBoxFactor n d * B) ≤
      (Real.exp (projectionLogConstant n) * (projectionLogConstant n + 1)) * curveBound d B := by
  let A := projectionBoxFactor n d
  let C := projectionLogConstant n
  have hA := zero_lt_one.trans_le (projectionBoxFactor_one_le n d)
  have hB' := zero_lt_one.trans_le hB
  have hC := projectionLogConstant_nonneg n
  have hlog : Real.log A + Real.log B + d ≤ (C + 1) * (Real.log B + d) := by
    have := projectionBoxFactor_log_le n hd
    have hh := mul_nonneg hC (Real.log_nonneg hB)
    change Real.log A ≤ C * d at this
    nlinarith
  change curveBound d (A * B) ≤ _
  unfold curveBound
  rw [Real.mul_rpow hA.le hB'.le, Real.log_mul hA.ne' hB'.ne']
  calc
    _ ≤ (d : ℝ) ^ 3 * (Real.exp C * B ^ (1 / (d : ℝ))) *
        ((C + 1) * (Real.log B + d)) := by
      have hpow := projectionBoxFactor_rpow_le n hd zero_le_one
      rw [one_mul] at hpow
      have := Real.log_nonneg (projectionBoxFactor_one_le n d)
      have := Real.log_nonneg hB
      gcongr
    _ = _ := by dsimp [C]; ring

end
end CCDN
