/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Projection.DegreePreservingProjectionBox
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Determinant.PolynomialMapDeterminant
import CCDN.Projection.BoundedDegreePreservingProjection

/-! Reduce the integral-point count of an arbitrary prime affine curve
to the proved plane count, using the constructed degree-preserving projection. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- An integral affine curve of degree `d` has an irreducible plane equation `f` of degree
`d` such that, for every radius `B ≥ 1`, its integral points of height at most `B` number at
most those of `f` in a box enlarged by `projectionBoxFactor n d`, plus `d(d-1)`. -/
theorem exists_plane_count_reduction {n : ℕ}
    (I : Ideal (CoordinatePolynomial n)) [I.IsPrime]
    (d : ℕ) (hd : 0 < d) (hdegree : HasAffineCurveDegree I d) :
    ∃ f : CoordinatePolynomial 2, Irreducible f ∧ f.totalDegree = d ∧
      ∀ B : ℝ, 1 ≤ B → count (idealZeroLocus I) B ≤
        count (zeroLocus f) (projectionBoxFactor n d * B) + d * (d - 1) := by
  classical
  obtain ⟨P, f, hP, hf, hfd, hrel, hcount⟩ := exists_bounded_projection_card_le I hd hdegree
  refine ⟨f, hf, hfd, fun B hB => ?_⟩
  let S := integralPoints (idealZeroLocus I) B
  let T := S.image (P *ᵥ ·)
  have hc := hcount (S.image rationalPoint) (by
    rintro _ hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact (mem_integralPoints.mp hx).2)
  have he : T.image rationalPoint = (S.image rationalPoint).image (fun z j => eval z (integerLinearForm (P j))) := by
    simp [T, Finset.image_image, Function.comp_def, rationalPoint_integer_projection]
  rw [Finset.card_image_of_injective S (rationalPoint_injective n), ← he,
    Finset.card_image_of_injective T (rationalPoint_injective 2)] at hc
  apply hc.trans (Nat.add_le_add_right (Finset.card_le_card ?_) _)
  rintro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hxB,hxI⟩ := mem_integralPoints.mp hx
  refine mem_integralPoints.mpr ⟨degreeProjection_box P hd hP (by linarith) hxB, ?_⟩
  change eval (rationalPoint _) f = 0
  rw [rationalPoint_integer_projection, ← eval_polynomial_coordinate_map]
  exact hxI _ hrel

end
end CCDN
