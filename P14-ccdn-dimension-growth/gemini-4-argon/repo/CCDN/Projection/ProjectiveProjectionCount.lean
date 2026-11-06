/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveChartIdeal
public import CCDN.Projection.DegreePreservingProjectionBox
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.Projection.BoundedDegreePreservingProjection
import CCDN.Projection.ProjectivePlaneProjection

/-! A projective curve with a proper standard chart reduces to a plane
equation of the same degree. Projection loses at most d(d-1) affine points
and at most d further points lie on the omitted hyperplane. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A projective curve of degree `d > 0` in `ℙⁿ`, given by a prime ideal `I` not containing
`X 0`, has at most `d ^ 2` more rational points of height at most `B` than some irreducible
projective plane curve of degree `d` has of height at most `projectionBoxFactor n d * B`. -/
theorem exists_projective_plane_count_reduction {n d : ℕ}
    (I : Ideal (CoordinatePolynomial (n + 1))) [I.IsPrime] (hX : X 0 ∉ I)
    (hd : 0 < d) (hdegree : HasProjectiveCurveDegree I d) :
    ∃ f : MvPolynomial (Fin 3) ℚ, f.IsHomogeneous d ∧ Irreducible f ∧
      ∀ B : ℝ, 1 ≤ B →
        projectiveCount (projectiveIdealZeroLocus I) B ≤
          projectiveCount (projectiveZeroLocus f) (projectionBoxFactor n d * B) + d ^ 2 := by
  /- Let `I` be a prime ideal defining a projective curve of degree `d` not contained in the
  hyperplane `X₀ = 0`, and suppose the moment coordinates with parameters `k₀ ≤ n ^ 2 * d` and
  `k₁ ≤ n * d ^ 2` satisfy the plane relation `f` of degree `d` on its affine chart, losing at most
  `d * (d - 1)` points on any finite set of chart points. Then the curve has at most `d ^ 2` more
  rational points of height at most `B` than the projective plane curve defined by the homogenization
  of `f` has of height at most `projectionBoxFactor n d * B`. -/
  classical
  let J := projectiveChartIdeal I
  obtain ⟨k₀, k₁, f, hk₀, hk₁, hfir, hfd, hker, hcount⟩ :=
    exists_bounded_projection_card_le J d hd (projectiveChartIdeal_degree I hX hdegree)
  have hfI : aeval ![momentCoordinate ℚ n k₀, momentCoordinate ℚ n k₁] f ∈ J :=
    (hker f).mpr dvd_rfl
  refine ⟨scaledHomogenize d 1 f, scaledHomogenize_homogeneous 1 f hfd.le,
    by simpa only [hfd] using scaledHomogenize_irreducible f hfir one_ne_zero, fun B hB => ?_⟩
  let S := projectivePoints (projectiveIdealZeroLocus I) B
  let T := S.filter (fun x => x.rep 0 ≠ 0)
  let U := S.filter (fun x => ¬ x.rep 0 ≠ 0)
  let R := T.image projectiveAffineCoordinates
  let π : RatPoint n → RatPoint 2 := fun z =>
    ![eval z (momentCoordinate ℚ n k₀), eval z (momentCoordinate ℚ n k₁)]
  have hc : T.card ≤ (R.image π).card + d * (d - 1) := by
    rw [← Finset.card_image_of_injOn fun x hx y hy he =>
      projectiveAffineCoordinates_injective (Finset.mem_filter.mp hx).2
        (Finset.mem_filter.mp hy).2 he]
    exact hcount R fun z hz => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
      exact projectiveChartIdeal_point I hX x (mem_projectivePoints.mp hxS).2 hx0
  have himage : (R.image π).card ≤
      projectiveCount (projectiveZeroLocus (scaledHomogenize d 1 f))
        (projectionBoxFactor n d * B) := by
    rw [← Finset.card_image_of_injective (R.image π) (affineProjectivePoint_injective 2)]
    refine Finset.card_le_card fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxB, hxI⟩ := mem_projectivePoints.mp hxS
    exact mem_projectivePoints.mpr
      ⟨projectivePlaneChartProjection_height hk₀ hk₁ x hx0 hB hxB,
        projectivePlaneChartProjection_zero I hX f hfd hfI x hxI hx0⟩
  have hU : U.card ≤ d := by
    simpa only [Fintype.card_coe, mul_one] using
      projective_section_card_le_degree I hdegree (X 0) (isHomogeneous_X _ _)
        hX (fun x : U => x.val) Subtype.val_injective
        (fun x => (mem_projectivePoints.mp (Finset.mem_filter.mp x.property).1).2)
        (fun x => by simpa using (Finset.mem_filter.mp x.property).2)
  have hsum : T.card + U.card = S.card := Finset.card_filter_add_card_filter_not _
  have hdcalc : d * (d - 1) + d = d ^ 2 := by have := Nat.sub_add_cancel hd; nlinarith
  change S.card ≤ _
  omega

end
end CCDN
