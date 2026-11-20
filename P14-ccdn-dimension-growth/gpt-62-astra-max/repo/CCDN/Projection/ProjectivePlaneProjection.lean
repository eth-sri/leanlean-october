/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveChartIdeal
public import CCDN.Projection.DegreePreservingProjectionBox
import CCDN.Determinant.PolynomialMapDeterminant
import CCDN.Height.ProjectiveIntegerHeight

/-! The bounded integral affine projection lifts to a projective plane
map on the standard chart, with the same polynomial height factor. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- For an integer vector `z` with `z 0 ≠ 0`, the projective point `[1 : z 1 / z 0 : …]` is the
point with homogeneous coordinates `z`. -/
lemma affineProjectivePoint_eq_integer {n : ℕ} (z : IntPoint (n + 1)) (hz0 : z 0 ≠ 0) :
    affineProjectivePoint (fun j => (z j.succ : ℚ) / (z 0 : ℚ)) =
      Projectivization.mk ℚ (rationalPoint z)
        (rationalPoint_ne_zero (fun h => hz0 (congrFun h 0))) := by
  have h0 := by exact_mod_cast hz0
  apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mpr
  refine ⟨(z 0)⁻¹, ?_⟩
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  simp [rationalPoint, h0]
  solve_by_elim [mul_comm]

/-- The height loss on the standard chart is the same operator-norm factor
as for the affine integer projection. -/
theorem projectivePlaneChartProjection_height {n d : ℕ} (P : Matrix (Fin 2) (Fin n) ℤ)
    (hd : 0 < d) (hP : ∀ i j, |P i j| ≤ integerBirationalProjectionHeight n d)
    (x : ProjectivePoint n) (hx : x.rep 0 ≠ 0) {B : ℝ} (hB : 1 ≤ B) (hxB : x.mulHeight ≤ B) :
    (affineProjectivePoint fun i => eval (projectiveAffineCoordinates x) (integerLinearForm (P i))).mulHeight ≤
      projectionBoxFactor n d * B := by
  let z := primitiveProjectiveRep x
  obtain ⟨hz0, hchart⟩ := primitiveProjectiveRep_chart x hx
  let w : IntPoint 3 := Fin.cons (z 0) (P *ᵥ fun j => z j.succ)
  have hw0 := hz0
  have hcoord : (fun i => eval (projectiveAffineCoordinates x) (integerLinearForm (P i))) =
      fun i => (w i.succ : ℚ) / (w 0 : ℚ) := by
    simp_rw [hchart, eval_linearForm, w, z, Fin.cons_zero, Fin.cons_succ, Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_div, mul_div_assoc]
  rw [hcoord, affineProjectivePoint_eq_integer w hw0]
  apply projective_integer_height_le w (fun h => hw0 (congrFun h 0))
  exact Fin.cases (((primitiveProjectiveRep_bound x 0).trans hxB).trans
    (le_mul_of_one_le_left (by linarith) (projectionBoxFactor_one_le n d)))
    (degreeProjection_box P hd hP (by linarith) (fun j => (primitiveProjectiveRep_bound x j.succ).trans hxB))

end
end CCDN
