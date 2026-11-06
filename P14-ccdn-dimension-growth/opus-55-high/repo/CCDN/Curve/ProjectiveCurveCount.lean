/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Plane.ProjectivePlaneAbsoluteCount
import CCDN.Projection.ScaleAbsorption
import CCDN.Algebra.ProjectivePermutation
import CCDN.Plane.ProjectivePlaneLinearCount
import CCDN.Projection.ProjectiveProjectionCount

/-! The projective curve count of Theorem 2 with an explicit constant. In a chart where the
curve is not contained in the hyperplane at infinity, a bounded projection to the plane and the
projective plane count give the bound (`projective_curve_count_of_proper_chart`); a coordinate
permutation, which costs no height, chooses such a chart (`projective_curve_count`). -/

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

theorem projectiveCurveEstimate_scale {d : ℕ} (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    projectiveCurveEstimate d (projectionBoxFactor n d * B) ≤
      Real.exp (2 * projectionLogConstant n) * projectiveCurveEstimate d B := by
  have hA : 0 < projectionBoxFactor n d :=
    lt_of_lt_of_le (by norm_num) (projectionBoxFactor_one_le n d)
  have hpow : (projectionBoxFactor n d) ^ (2 / (d : ℝ)) ≤
      Real.exp (2 * projectionLogConstant n) := by
    rw [Real.rpow_def_of_pos hA, Real.exp_le_exp, ← mul_div_assoc]
    apply (div_le_iff₀ (mod_cast hd)).mpr
    have hlog := projectionBoxFactor_log_le n hd
    linarith
  unfold projectiveCurveEstimate
  rw [Real.mul_rpow hA.le (by linarith)]
  have h := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) by positivity)
  convert h using 1 <;> ring

end

variable {n d : ℕ} (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime] {B : ℝ}

/-- Let `I` be the homogeneous prime ideal of a projective curve of degree `d > 0` in `ℙⁿ` that is
not contained in the hyperplane `X 0 = 0` (that is, `X 0 ∉ I`). For `B ≥ 1`, the number of rational
points of height at most `B` on the curve is at most `projectiveCurveConstant n * d⁴ B^(2/d)`. -/
theorem projective_curve_count_of_proper_chart
    (hX : X 0 ∉ I)
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) (hB : 1 ≤ B) :
    (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCurveConstant n * projectiveCurveEstimate d B := by
  obtain ⟨f, hf, hir, hreduce⟩ : ∃ f : MvPolynomial (Fin 3) ℚ, f.IsHomogeneous d ∧ Irreducible f ∧
      ∀ B : ℝ, 1 ≤ B →
        projectiveCount (projectiveIdealZeroLocus I) B ≤
          projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) + d ^ 2 := by
    classical
    let J := projectiveChartIdeal I
    have hJ : HasAffineCurveDegree (projectiveChartIdeal I) d := by
      apply projective_chart_degree I _ (IsFractionRing.injective _ _) _ hdegree
      intro h
      exact hX (Ideal.Quotient.eq_zero_iff_mem.mp (by simp_all))
    obtain ⟨k₀, k₁, f, hk₀, hk₁, hfir, hfd, hker, hcount⟩ :=
      exists_bounded_projection_card_le J d hd hJ
    have hfI :=
      (hker f).mpr dvd_rfl
    refine ⟨scaledHomogenize d 1 f, scaledHomogenize_homogeneous 1 f hfd.le, ?_,
      fun B hB => ?_⟩
    · simpa [hfd] using scaledHomogenize_irreducible f hfir one_ne_zero
    let S := projectivePoints (projectiveIdealZeroLocus I) B
    let T := S.filter (fun x => x.rep 0 ≠ 0)
    let U := S.filter (fun x => ¬ x.rep 0 ≠ 0)
    let R := T.image projectiveAffineCoordinates
    let π : RatPoint n → RatPoint 2 := fun z =>
      ![eval z (momentCoordinate ℚ n k₀), eval z (momentCoordinate ℚ n k₁)]
    have hR : ∀ z ∈ R, z ∈ idealZeroLocus J := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
      exact projectiveChartIdeal_point I hX x (mem_projectivePoints.mp hxS).2 hx0
    have hc := hcount R hR
    have hRT : R.card = T.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy he
      exact projectiveAffineCoordinates_injective (Finset.mem_filter.mp hx).2
        (Finset.mem_filter.mp hy).2 he
    rw [hRT] at hc
    change _ ≤ (R.image π).card + _ at hc
    have himage : (R.image π).card ≤
        projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f))
          (projectionBoxFactor n d * B) := by
      rw [← Finset.card_image_of_injective (R.image π) (affineProjectivePoint_injective 2)]
      apply Finset.card_le_card
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxB, hxI⟩ := mem_projectivePoints.mp hxS
      exact mem_projectivePoints.mpr
        ⟨projectivePlaneChartProjection_height hk₀ hk₁ x hx0 hB hxB,
          projectivePlaneChartProjection_zero I hX f hfd hfI x hxI hx0⟩
    have hU : U.card ≤ d := by
      have h := projective_section_card_le_degree I hdegree (X 0) (isHomogeneous_X _ _)
        hX (fun x : U => x.val) Subtype.val_injective
        (fun x => (mem_projectivePoints.mp (Finset.mem_filter.mp x.property).1).2)
        (fun x => by aesop)
      simp_all
    have hsum : T.card + U.card = S.card := Finset.card_filter_add_card_filter_not _
    have hdcalc : d * (d - 1) + d = d ^ 2 := by
      have h := Nat.sub_add_cancel hd
      nlinarith
    change S.card ≤ _
    omega
  have hAB := one_le_mul_of_one_le_of_one_le (projectionBoxFactor_one_le n d) hB
  have hplane := projective_plane_equation_bound f hf hd hir hAB
  have hR : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) + d ^ 2 := by
    exact_mod_cast hreduce B hB
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hQ : 1 ≤ B ^ (2 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have herr : d ^ 2 ≤ projectiveCurveEstimate d B :=
    (pow_le_pow_right₀ hd1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) hQ)
  calc
    _ ≤ projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) +
        (d : ℝ) ^ 2 := hR
    _ ≤ projectivePlaneAbsoluteConstant *
          projectiveCurveEstimate d (projectionBoxFactor n d * B) +
        projectiveCurveEstimate d B := by
      rw [projectiveCurveEstimate, ← mul_assoc]
      exact add_le_add hplane herr
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
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) (hB : 1 ≤ B) :
    (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      projectiveCurveConstant n * projectiveCurveEstimate d B := by
  by_cases hS : (projectivePoints (projectiveIdealZeroLocus I) B).Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hxI := (mem_projectivePoints.mp hx).2
    obtain ⟨j, hj⟩ := Function.ne_iff.mp x.rep_nonzero
    let e := Equiv.swap (0 : Fin (n + 1)) j
    let J := projectivePermutedIdeal I e
    have hJ : HasProjectiveCurveDegree (projectivePermutedIdeal I e) d := by
      obtain ⟨N, c, hN⟩ := hdegree
      exact ⟨N, c, fun M hM => by simp_all [projectiveHilbertFunction_permuted]⟩
    have h := projective_curve_count_of_proper_chart J (by
      intro h
      have hh := (mem_projectivePermutedIdeal I e (X 0)).mp h
      have hz := projectiveIdealZeroLocus_rep hxI (X j) (by aesop)
      simp_all) hd hJ hB
    have hc : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        projectiveCount (projectiveIdealZeroLocus J) B := by
      exact_mod_cast projectiveCount_le_permuted I e B
    grind
  · have he := Finset.not_nonempty_iff_eq_empty.mp hS
    unfold projectiveCount
    rw [he, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (projectiveCurveConstant_pos n).le
      (by unfold projectiveCurveEstimate; positivity)

