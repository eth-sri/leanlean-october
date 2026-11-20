/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.AffineMinimum
import CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight
import CCDN.ForMathlib.Log

/-! Translating the affine box by a vector bounded by the degree costs only
 a dimension constant in the coefficient-sensitive minimum bound. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- The bounded translation used to obtain a nonzero constant coefficient costs
only a dimension-dependent factor. -/
theorem affineAuxiliaryDegreeExpression_translation {n d : ℕ} (hd : 0 < d)
    {B L b : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineAuxiliaryDegreeExpression n d (B + d) L b ≤
      (2 * Real.exp ((n : ℝ) + 2)) * affineAuxiliaryDegreeExpression n d B L b := by
  
  have hlog := Real.log_le_log (by positivity : 0 < B + d)
    (show B + d ≤ B * ((d : ℝ) + 1) by nlinarith)
  rw [Real.log_mul (by linarith) (by positivity)] at hlog
  have hlogB := Real.log_nonneg hB
  have hlogB' := Real.log_nonneg (show 1 ≤ B + d by linarith)
  let W := b / L ^ heightExponent n d
  let M := min (1 + Real.log B / d) W
  have hM : 0 ≤ M := by positivity
  have hmin : min (1 + Real.log (B + d) / d) W ≤ 2 * M := by
    dsimp only [M]
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    apply le_min
    · refine (min_le_left _ _).trans ?_
      have h := Real.log_add_one_le_self (Nat.cast_nonneg (α := ℝ) d)
      field_simp
      linarith
    grind
  have hp : (B + d) ^ (1 / degreeRoot n d) ≤ Real.exp ((n : ℝ) + 2) * B ^ (1 / degreeRoot n d) := by
    refine (Real.rpow_le_rpow (by positivity) (show B + d ≤ ((d : ℝ) + 1) * B by nlinarith) (by positivity)).trans ?_
    rw [Real.mul_rpow (by positivity) (by positivity)]
    gcongr
    simpa only [one_mul] using degreeRoot_weight_power_le (n := n) hd zero_le_one
  let E := auxDegreeScale n d
  calc
    _ = E * (B + d) ^ (1 / degreeRoot n d) * (min (1 + Real.log (B + d) / d) W + 2) := rfl
    _ ≤ E * (Real.exp ((n : ℝ) + 2) * B ^ (1 / degreeRoot n d)) * (2 * (M + 2)) := by
      gcongr
      linarith
    _ = _ := by unfold affineAuxiliaryDegreeExpression; ring

end
end CCDN
