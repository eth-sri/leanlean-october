import RequestProject.QCubeThreeOrderedCoordinates
import RequestProject.CubicalThreeOrientationChain


/-! The indexed oriented six-face chain subdivides to the actual three-cube boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qThreeOrientedFaces_subdivision (c : QCube A) u v w
    huv (hvw : w < v) hs :
    qSquareChainSubdivision
      (Finsupp.lmapDomain ℤ ℤ
        (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) threeOrientedFaces) =
      cubeThreeSquareBoundary c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs := by
  classical
  let f := qThreeFaceSquare c u v w (Ne.symm huv.ne)
    (by grind) (Ne.symm hvw.ne) hs
  have h0 (s : ZMod 2) : qSquareChainSubdivision (Finsupp.single (f (0, s)) 1) =
      cubeSquareSubdivision _ v w (Ne.symm hvw.ne)
        (threeFacet_vw_spx c (Ne.symm huv.ne) (by grind) hs s) := by
    rw [qSquare_subdivision_single _ 1 hvw
      _]
    aesop
  have h1 (s : ZMod 2) : qSquareChainSubdivision (Finsupp.single (f (1, s)) 1) =
      cubeSquareSubdivision _ u w (by grind)
        (threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s) := by
    rw [qSquare_subdivision_single _ 1 (hvw.trans huv)
      _]
    aesop
  have h2 (s : ZMod 2) : qSquareChainSubdivision (Finsupp.single (f (2, s)) 1) =
      cubeSquareSubdivision _ u v (Ne.symm huv.ne)
        (threeFacet_uv_spx c (by grind) (Ne.symm hvw.ne) hs s) := by
    rw [qSquare_subdivision_single _ 1 huv
      _]
    aesop
  simp [threeOrientedFaces, map_sub, map_add,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [h0, h0, h1, h1, h2, h2]
  unfold cubeThreeSquareBoundary
  abel

/-- Every actual square cycle supported on a three-cube's facets subdivides to a scalar
multiple of its actual oriented cubical boundary. -/
theorem qThreeFacetCycle_subdivision c u v w
    huv (hvw : w < v) hs
    (r : QSquare A →₀ ℤ) (hr : ∀ s ∈ r.support, s.1 < c)
    (hcycle : qSquareCubicalBoundary r = 0) :
    ∃ k : ℤ, qSquareChainSubdivision r = k •
      cubeThreeSquareBoundary c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs := by
  classical
  let f := qThreeFaceSquare c u v w (Ne.symm huv.ne)
    (by grind) (Ne.symm hvw.ne) hs
  let z := qThreeOrderedCoordinates c u v w (Ne.symm huv.ne)
    (by grind) (Ne.symm hvw.ne) hs r
  have hrecon : Finsupp.lmapDomain ℤ ℤ f z = r :=
    qThreeOrderedCoordinates_reconstruct c u v w _
      _ _ hs r hr
  have hz : qSquareCubicalBoundary (Finsupp.lmapDomain ℤ ℤ f z) = 0 := by
    simp_all
  have hcoeff := qThreeFace_cycle_coefficients c u v w huv hvw hs z hz
  have he : z = z (0, 0) • threeOrientedFaces := by
    ext i
    rw [Finsupp.smul_apply, threeOrientedFaces_apply, hcoeff i]
    rfl
  refine ⟨z (0, 0), ?_⟩
  conv_lhs => rw [← hrecon, he, map_smul, map_smul]
  exact congrArg _ (qThreeOrientedFaces_subdivision c u v w huv hvw hs)
