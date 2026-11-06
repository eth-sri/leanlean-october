/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Plane.ProjectivePlaneAbsoluteCount
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Algebra.ProjectiveAffineChart
import CCDN.ForMathlib.MvPolynomial
import CCDN.Plane.NonabsolutePlaneCount
import CCDN.Plane.ProjectivePlaneBezout

/-! Curves that are irreducible over the base field but split over an
extension have at most d^2+d projective base-field points. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The uniform plane bound for every rational irreducible homogeneous
equation of degree at least two, whether or not geometrically irreducible. -/
theorem projective_plane_rational_count {d : ℕ}
    (f : MvPolynomial (Fin 3) ℚ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible f) {B : ℝ} (hB : 1 ≤ B) :
    (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤
      projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * B ^ (2 / (d : ℝ)) := by
  classical
  by_cases habs : AbsolutelyIrreducibleRat f
  · exact projective_plane_rational_absolute_count f hf hd habs hB
  · let K := AlgebraicClosure ℚ
    have hX := variable_not_dvd_irreducible_homogeneous f hf hir hd 0
    have hdeg := affineChart_degree_of_not_variable_dvd f hf hX
    have hchart := affineChart_irreducible_of_not_variable_dvd f hf hir hX
    have hchartred : ¬ Irreducible (map (algebraMap ℚ K) (affineChart 2 f)) := fun hi =>
      habs <| irreducible_of_affineChart_irreducible _
        (by
          rw [affineChart_map, totalDegree_map_of_injective (algebraMap ℚ K).injective,
            hdeg, (hf.map _).totalDegree]
          exact fun h => hir.ne_zero
            ((map_injective (algebraMap ℚ K) (algebraMap ℚ K).injective) (by simpa using h)))
        (by rwa [affineChart_map])
    let P := projectivePoints (projectiveZeroLocus f) B
    let z : P → Projectivization ℚ (Fin 3 → ℚ) := Subtype.val
    let S := Finset.univ.filter (fun i : P => (z i).rep 0 ≠ 0)
    let T := Finset.univ.filter (fun i : P => ¬ (z i).rep 0 ≠ 0)
    have hs := nonabsolute_plane_points_card_le (affineChart 2 f) hchart
      (by omega : 0 < (affineChart 2 f).totalDegree) hchartred
      (fun i : S => projectiveAffineCoordinates (z i.val))
      (fun i j he => Subtype.ext (Subtype.val_injective (projectiveAffineCoordinates_injective
        (Finset.mem_filter.mp i.property).2 (Finset.mem_filter.mp j.property).2 he)))
      (fun i => projectiveAffineCoordinates_zero f hf (z i.val)
        (Finset.mem_filter.mp i.property).2 (mem_projectivePoints.mp i.val.property).2)
    have ht := projective_plane_common_zeros_card_le f (X 0) hf hir (isHomogeneous_X _ _)
      (irreducible_homogeneous_not_dvd_variable f hf hir hd 0)
      (fun i : T => z i.val) (Subtype.val_injective.comp Subtype.val_injective)
      (fun i => (mem_projectivePoints.mp i.val.property).2)
      (fun i => by change eval (z i.val).rep (X 0) = 0; simpa using (Finset.mem_filter.mp i.property).2)
    have hsum := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun i : P => (z i).rep 0 ≠ 0)
    simp only [Fintype.card_coe, hdeg] at hs
    simp only [Fintype.card_coe, mul_one] at ht
    change S.card + T.card = Finset.univ.card at hsum
    rw [Finset.card_univ, Fintype.card_coe] at hsum
    have h : projectiveCount (projectiveZeroLocus f) B ≤ d ^ 2 + d := by
      change P.card ≤ _; omega
    have hR : (projectiveCount (projectiveZeroLocus f) B : ℝ) ≤ (d : ℝ) ^ 2 + d := mod_cast h
    have hd1 : (1 : ℝ) ≤ d := mod_cast (show 1 ≤ d by omega)
    have hd4 : (d : ℝ) ^ 2 + d ≤ 2 * (d : ℝ) ^ 4 := by nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
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
      _ ≤ 2 * (d : ℝ) ^ 4 := hd4
      _ ≤ projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ ≤ _ := le_mul_of_one_le_right
        (mul_nonneg projectivePlaneAbsoluteConstant_pos.le (by positivity)) hQ

end
end CCDN
