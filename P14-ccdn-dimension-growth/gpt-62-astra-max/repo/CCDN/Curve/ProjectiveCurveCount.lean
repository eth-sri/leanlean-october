/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.ScaleAbsorption
import CCDN.Algebra.ProjectivePermutation
public import CCDN.Plane.ProjectivePlaneCount
import CCDN.Projection.ProjectiveProjectionCount

/-! The projective curve count of Theorem 2 with an explicit constant. In a chart where the
curve is not contained in the hyperplane at infinity, a bounded projection to the plane and the
projective plane count give the bound (`projective_curve_count_of_proper_chart`); a coordinate
permutation, which costs no height, chooses such a chart (`projective_curve_count`). -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

section

variable (n : ℕ)

/-- The explicit constant `projectivePlaneAbsoluteConstant * exp (2 * projectionLogConstant n) + 1`
of the projective curve count in `ℙⁿ`: the plane-curve constant, enlarged by the height loss of a
bounded projection to the plane, plus one to absorb the `d²` error term of the projection. -/
def projectiveCurveConstant : ℝ :=
  projectivePlaneAbsoluteConstant * Real.exp (2 * projectionLogConstant n) + 1

/-- The constant `projectiveCurveConstant n` is positive. -/
lemma projectiveCurveConstant_pos : 0 < projectiveCurveConstant n := by
  unfold projectiveCurveConstant
  have := projectivePlaneAbsoluteConstant_pos
  positivity

private theorem projectiveCurveEstimate_scale {d : ℕ} (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    projectiveCurveEstimate d (projectionBoxFactor n d * B) ≤
      Real.exp (2 * projectionLogConstant n) * projectiveCurveEstimate d B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 < projectionBoxFactor n d :=
    lt_of_lt_of_le (by norm_num) (projectionBoxFactor_one_le n d)
  have hpow : (projectionBoxFactor n d) ^ (2 / (d : ℝ)) ≤
      Real.exp (2 * projectionLogConstant n) := by
    rw [Real.rpow_def_of_pos hA, Real.exp_le_exp, ← mul_div_assoc]
    apply (div_le_iff₀ hd0).mpr
    linarith [projectionBoxFactor_log_le n hd]
  unfold projectiveCurveEstimate
  rw [Real.mul_rpow hA.le (by linarith)]
  have h := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ d ^ 4 * B ^ (2 / (d : ℝ)) by positivity)
  convert h using 1 <;> ring

end

variable {n d : ℕ} (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime]

/-- Let `I` be the homogeneous prime ideal of a projective curve of degree `d > 0` in `ℙⁿ` that is
not contained in the hyperplane `X 0 = 0` (that is, `X 0 ∉ I`). For `B ≥ 1`, the number of rational
points of height at most `B` on the curve is at most `projectiveCurveConstant n * d⁴ B^(2/d)`. -/
theorem projective_curve_count_of_proper_chart (hX : X 0 ∉ I)
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCurveConstant n * projectiveCurveEstimate d B := by
  obtain ⟨f, hf, hir, hreduce⟩ := exists_projective_plane_count_reduction I hX hd hdegree
  have hR : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) + (d : ℝ) ^ 2 := by
    exact_mod_cast hreduce B hB
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have herr : (d : ℝ) ^ 2 ≤ projectiveCurveEstimate d B :=
    (pow_le_pow_right₀ hd1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hB (by positivity)))
  calc
    _ ≤ projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) +
        (d : ℝ) ^ 2 := hR
    _ ≤ projectivePlaneAbsoluteConstant *
          projectiveCurveEstimate d (projectionBoxFactor n d * B) +
        projectiveCurveEstimate d B := by
      rw [projectiveCurveEstimate, ← mul_assoc]
      exact add_le_add (projective_plane_equation_bound f hf hd hir (one_le_mul_of_one_le_of_one_le (projectionBoxFactor_one_le n d) hB)) herr
    _ ≤ projectivePlaneAbsoluteConstant *
          (Real.exp (2 * projectionLogConstant n) * projectiveCurveEstimate d B) +
        projectiveCurveEstimate d B := by
      gcongr
      exacts [projectivePlaneAbsoluteConstant_pos.le, projectiveCurveEstimate_scale n hd hB]
    _ = projectiveCurveConstant n * projectiveCurveEstimate d B := by
      unfold projectiveCurveConstant
      ring

/-- Let `I` be the homogeneous prime ideal of a projective curve of degree `d > 0` in `ℙⁿ`. For
`B ≥ 1`, the number of rational points of height at most `B` on the curve is at most
`projectiveCurveConstant n * d⁴ B^(2/d)`. -/
theorem projective_curve_count
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCurveConstant n * projectiveCurveEstimate d B := by
  classical
  by_cases hS : (projectivePoints (projectiveIdealZeroLocus I) B).Nonempty
  · obtain ⟨x, hx⟩ := hS
    obtain ⟨j, hj⟩ := Function.ne_iff.mp x.rep_nonzero
    let e := Equiv.swap 0 j
    let J := projectivePermutedIdeal I e
    have hX : X 0 ∉ J := by
      intro h
      have hXj := by simpa using ((mem_projectivePermutedIdeal I e (X 0)).mp h)
      exact hj (by simpa using (projectiveIdealZeroLocus_rep ((mem_projectivePoints.mp hx).2) (X j) hXj))
    have hc : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        projectiveCount (projectiveIdealZeroLocus J) B := by
      exact_mod_cast projectiveCount_le_permuted I e B
    exact hc.trans (projective_curve_count_of_proper_chart J hX hd (projectiveCurveDegree_permuted I e hdegree) hB)
  · unfold projectiveCount
    rw [(Finset.not_nonempty_iff_eq_empty.mp hS), Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (projectiveCurveConstant_pos n).le
      (by unfold projectiveCurveEstimate; positivity)

end
end CCDN
