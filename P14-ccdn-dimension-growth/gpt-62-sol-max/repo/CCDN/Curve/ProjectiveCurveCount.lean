/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.ProjectivePlaneCount
public import CCDN.Projection.ScaleAbsorption
import CCDN.Projection.ProjectiveProjectionCount

/-! The projective curve count of Theorem 2 with an explicit constant. In a chart where the
curve is not contained in the hyperplane at infinity, a bounded projection to the plane and the
projective plane count give the bound (`projective_curve_count_of_proper_chart`); a coordinate
permutation, which costs no height, chooses such a chart (`projective_curve_count`). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The explicit constant `projectivePlaneAbsoluteConstant * exp (2 * projectionLogConstant n) + 1`
of the projective curve count in `ℙⁿ`: the plane-curve constant, enlarged by the height loss of a
bounded projection to the plane, plus one to absorb the `d²` error term of the projection. -/
def projectiveCurveConstant (n : ℕ) : ℝ :=
  projectivePlaneAbsoluteConstant * Real.exp (2 * projectionLogConstant (n + 1)) + 1

/-- The constant `projectiveCurveConstant n` is positive. -/
lemma projectiveCurveConstant_pos (n : ℕ) : 0 < projectiveCurveConstant n := by
  unfold projectiveCurveConstant
  have := projectivePlaneAbsoluteConstant_pos
  positivity

private theorem projectiveCurveEstimate_scale (n : ℕ) {d : ℕ} (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    projectiveCurveEstimate d (projectionBoxFactor n d * B) ≤
      Real.exp (2 * projectionLogConstant n) * projectiveCurveEstimate d B := by
  have hpow := projectionBoxFactor_rpow_le n hd (show (0 : ℝ) ≤ 2 by norm_num)
  unfold projectiveCurveEstimate
  rw [Real.mul_rpow (zero_le_one.trans (projectionBoxFactor_one_le n d)) (by linarith)]
  have h := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) by positivity)
  convert h using 1 <;> ring

section

variable {n d : ℕ}
  (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]
include n d I

/-- The projective curve bound follows from the plane count by bounded projection. -/
theorem projective_curve_count (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d)
    {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCurveConstant n * projectiveCurveEstimate d B := by
  obtain ⟨f, hf, hir, hreduce⟩ := exists_projective_plane_count_reduction I hd hdegree
  have hAB := one_le_mul_of_one_le_of_one_le (projectionBoxFactor_one_le (n + 1) d) hB
  have hplane := projective_plane_equation_bound f hf hd hir hAB
  have hR : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCount (projectiveZeroLocus f) (projectionBoxFactor (n + 1) d * B) + (d : ℝ) ^ 2 := by
    exact_mod_cast hreduce B hB
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : 1 ≤ B ^ (2 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have herr : (d : ℝ) ^ 2 ≤ projectiveCurveEstimate d B :=
    (pow_le_pow_right₀ hd1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) hQ)
  calc
    _ ≤ projectiveCount (projectiveZeroLocus f) (projectionBoxFactor (n + 1) d * B) +
        (d : ℝ) ^ 2 := hR
    _ ≤ projectivePlaneAbsoluteConstant *
          projectiveCurveEstimate d (projectionBoxFactor (n + 1) d * B) +
        projectiveCurveEstimate d B := by
      rw [projectiveCurveEstimate, ← mul_assoc]
      exact add_le_add hplane herr
    _ ≤ projectivePlaneAbsoluteConstant *
          (Real.exp (2 * projectionLogConstant (n + 1)) * projectiveCurveEstimate d B) +
        projectiveCurveEstimate d B := by
      gcongr
      exacts [projectivePlaneAbsoluteConstant_pos.le, projectiveCurveEstimate_scale (n + 1) hd hB]
    _ = projectiveCurveConstant n * projectiveCurveEstimate d B := by
      unfold projectiveCurveConstant
      ring


end

end
end CCDN
