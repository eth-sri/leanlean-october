/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Plane.ProjectivePlaneAbsoluteCount
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Algebra.ProjectiveAffineChart
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.NonabsolutePlaneCount
import CCDN.Plane.ProjectivePlaneBezout

/-! Curves that are irreducible over the base field but split over an
extension have at most d^2+d projective base-field points. -/

namespace CCDN
section
open MvPolynomial

theorem nonabsolute_projective_plane_points_card_le {k K ι : Type*}
    [Field k] [Field K] [Algebra k K] [Fintype ι] [DecidableEq ι] {d : ℕ}
    (f : MvPolynomial (Fin 3) k) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible f) (hred : ¬ Irreducible (map (algebraMap k K) f))
    (z : ι → Projectivization k (Fin 3 → k)) (hinj : Function.Injective z)
    (hz : ∀ i, z i ∈ projectiveZeroLocus f) :
    Fintype.card ι ≤ d ^ 2 + d := by
  classical
  have hX := variable_not_dvd_irreducible_homogeneous f hf hir hd 0
  have hdeg := affineChart_degree_of_not_variable_dvd f hf hX
  have hchart := affineChart_irreducible_of_not_variable_dvd f hf hir hX
  have hchartred : ¬ Irreducible (map (algebraMap k K) (affineChart 2 f)) := by
    intro hi
    apply hred
    apply irreducible_of_affineChart_irreducible
    · rw [affineChart_map]
      have hmapdegree (q : MvPolynomial (Fin 2) k) :
          (map (algebraMap k K) q).totalDegree = q.totalDegree :=
          totalDegree_map_of_injective (algebraMap k K).injective _
      rw [hmapdegree, hdeg, (hf.map _).totalDegree]
      exact fun h => hir.ne_zero
        ((map_injective (algebraMap k K) (algebraMap k K).injective) (by grind))
    · rwa [affineChart_map]
  let S := Finset.univ.filter (fun i => (z i).rep 0 ≠ 0)
  let T := Finset.univ.filter (fun i : ι => ¬ (z i).rep 0 ≠ 0)
  have hs := nonabsolute_plane_points_card_le (affineChart 2 f) hchart
    (by grind) hchartred
    (fun i : S => projectiveAffineCoordinates (z i.val)) ?_ ?_
  · have ht := projective_plane_common_zeros_card_le f (X 0) hf hir (isHomogeneous_X _ _)
      (irreducible_homogeneous_not_dvd_variable f hf hir hd 0)
      (fun i : T => z i.val) (hinj.comp Subtype.val_injective) (fun i => hz i.val) ?_
    · have hsum := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (p := fun i => (z i).rep 0 ≠ 0)
      simp at hs
      simp at ht
      grind
    · intro i
      change eval (z i.val).rep (X 0) = 0
      simpa using (Finset.mem_filter.mp i.property).2
  · intro i j he
    apply Subtype.ext
    apply hinj
    exact projectiveAffineCoordinates_injective
      (Finset.mem_filter.mp i.property).2 (Finset.mem_filter.mp j.property).2 he
  · intro i
    exact projectiveAffineCoordinates_zero f hf (z i.val)
      (Finset.mem_filter.mp i.property).2 (hz i.val)

variable {d : ℕ} (f : MvPolynomial (Fin 3) ℚ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (hir : Irreducible f)
include hf hd hir

theorem projectiveCount_nonabsolute_plane_le
    {K : Type*} [Field K] [Algebra ℚ K]
    (hred : ¬ Irreducible (map (algebraMap ℚ K) f)) (B : ℝ) :
    projectiveCount (projectiveZeroLocus f) B ≤ d ^ 2 + d := by
  classical
  let S := projectivePoints (projectiveZeroLocus f) B
  have h := nonabsolute_projective_plane_points_card_le f hf hd hir hred
    (fun x : S => x.val) Subtype.val_injective (fun x => (mem_projectivePoints.mp x.property).2)
  simpa [Fintype.card_coe, S, projectiveCount] using h

/-- The uniform plane bound for every rational irreducible homogeneous
equation of degree at least two, whether or not geometrically irreducible. -/
theorem projective_plane_rational_count
    {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  by_cases habs : AbsolutelyIrreducibleRat f
  · have hf0 : f ≠ 0 := by aesop
    obtain ⟨g, a, hg, ha, he⟩ := exists_primitive_integer_model f hf0
    have hgh := rational_scalar_model_homogeneous he hf
    have hgi := rational_scalar_model_irreducible_charZero ha he habs
    have hzero : projectiveZeroLocus (map (Int.castRingHom ℚ) g) = projectiveZeroLocus f := by
      ext x
      exact rational_scalar_model_zero_iff ha he x.rep
    have h : (projectiveCount (projectiveZeroLocus (map (Int.castRingHom ℚ) g)) B : ℝ) ≤
        projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
      apply projective_zero_count_le_of_family_bound g hgh
      intro t z hz0 hinj hzprim hz hbox
      exact (projective_plane_finite_count_positioned g hgh hd hg hgi z hz0 hinj
        ⟨⟨hB, hz, hbox⟩, hzprim⟩).trans
        (show max ((d : ℝ) *
                scaledPlaneAuxiliaryDegreeBound d projectivePlaneDeterminantConstant (((d : ℝ) + 1) * B) 1)
              ((34 + 8 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 20)) *
                (d : ℝ) ^ 4) ≤
              projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) by
            have hd1 : (1 : ℝ) ≤ d := mod_cast (by omega)
            have hd0 : (0 : ℝ) < d := by positivity
            have hB0 : 0 < B := by linarith
            let Q := B ^ (2 / (d : ℝ))
            let E := 2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) *
                Real.exp 14
            let A := 34 + 8 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 20)
            have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
            have hE : 0 ≤ E := by positivity
            have hA : 0 ≤ A := by positivity
            have hlogplus := Real.log_add_one_le_self d.cast_nonneg
            have hlogR : Real.log (((d : ℝ) + 1) * B) ≤ d + Real.log B := by
              rw [Real.log_mul (by positivity) hB0.ne']
              linarith
            have hlogB : Real.log B ≤ (d : ℝ) / 2 * Q := by
              have h := Real.log_le_rpow_div hB0.le (show (0 : ℝ) < 2 / d by positivity)
              nlinarith
            have hpower : (((d : ℝ) + 1) * B) ^ (2 / (d : ℝ)) ≤ Real.exp 2 * Q := by
              rw [Real.mul_rpow (by positivity) hB0.le]
              apply mul_le_mul_of_nonneg_right ?_ (by positivity)
              rw [Real.rpow_def_of_pos (by positivity)]
              apply Real.exp_le_exp.mpr
              rw [← mul_div_assoc]
              apply (div_le_iff₀ hd0).mpr
              linarith
            have hd3 : (d : ℝ) ≤ (d : ℝ) ^ 3 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
            have hdQ : (d : ℝ) ≤ d * Q := by nlinarith
            have hd3Q :=
              mul_le_mul_of_nonneg_right hd3 (by positivity)
            have hrest : (d : ℝ) + Real.log (((d : ℝ) + 1) * B) + 2 ≤
                5 * (d : ℝ) ^ 3 * Q := by nlinarith
            have hterm := mul_le_mul_of_nonneg_left hpower
              (show 0 ≤ E * (d : ℝ) ^ 3 by positivity)
            have hdeg :
                scaledPlaneAuxiliaryDegreeBound d projectivePlaneDeterminantConstant (((d : ℝ) + 1) * B) 1 ≤
                (5 + E * Real.exp 2) * (d : ℝ) ^ 3 * Q := by
              unfold scaledPlaneAuxiliaryDegreeBound
              simp
              dsimp [E] at hterm ⊢
              nlinarith
            have hsmall := mul_le_mul_of_nonneg_left hdeg hd0.le
            have hlarge := mul_le_mul_of_nonneg_left hQ (show 0 ≤ A * (d : ℝ) ^ 4 by positivity)
            apply max_le
            · dsimp [projectivePlaneAbsoluteConstant]
              nlinarith [hsmall, mul_nonneg hA (mul_nonneg (pow_nonneg hd0.le 4)
                (show 0 ≤ Q by positivity))]
            · dsimp [projectivePlaneAbsoluteConstant]
              have hpositive : 0 ≤ (5 + E * Real.exp 2) * (d : ℝ) ^ 4 * Q := by positivity
              grind)
    rwa [hzero] at h
  · have h := projectiveCount_nonabsolute_plane_le f hf hd hir habs B
    have hR : (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤ d ^ 2 + d := by
      exact_mod_cast h
    have hd1 : (1 : ℝ) ≤ d := mod_cast (show 1 ≤ d by omega)
    have hC : 2 ≤ projectivePlaneAbsoluteConstant := by
      unfold projectivePlaneAbsoluteConstant
      have hpos := Real.exp_pos
        (heightDeterminantError projectivePlaneDeterminantConstant + 20)
      have hpos' : 0 ≤
          2 * Real.exp (heightDeterminantError projectivePlaneDeterminantConstant + 23) *
            Real.exp 14 * Real.exp 2 := by positivity
      linarith
    have hQ : 1 ≤ B ^ (2 / (d : ℝ)) := Real.one_le_rpow hB (by positivity)
    calc
      _ ≤ (d : ℝ) ^ 2 + d := hR
      _ ≤ 2 * (d : ℝ) ^ 4 := (by nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)])
      _ ≤ projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg projectivePlaneAbsoluteConstant_pos.le (by positivity)) hQ

