module

public import RequestProject.QCubeThreeOrderedCoordinates
public import RequestProject.CubicalThreeOrientationChain

@[expose] public section

/-! The indexed oriented six-face chain subdivides to the actual three-cube boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

variable (c : QThreeCube A)

noncomputable def qThreeCubicalFaceBoundary :=
  Finsupp.lmapDomain ℤ ℤ (qThreeFaceSquare c) threeOrientedFaces

/-- Every cycle on the facets is a multiple of the oriented cubical face chain. -/
theorem qThreeFacetCycle_scalar
    (r : QSquare A →₀ ℤ) (hr : ∀ s ∈ r.support, s.1 < c.1)
    (hcycle : qSquareCubicalBoundary r = 0) :
    ∃ k : ℤ, r = k • qThreeCubicalFaceBoundary c := by
  classical
  let f := qThreeFaceSquare c
  let z := qThreeOrderedCoordinates c r
  have hrecon : Finsupp.lmapDomain ℤ ℤ f z = r :=
    qThreeOrderedCoordinates_reconstruct c r hr
  have hz : qSquareCubicalBoundary (Finsupp.lmapDomain ℤ ℤ f z) = 0 := by
    rwa [hrecon]
  have he : z = z (0, 0) • threeOrientedFaces := by
    ext i
    rw [Finsupp.smul_apply, threeOrientedFaces_apply, (qThreeFace_cycle_coefficients c z hz) i]
    rfl
  refine ⟨z (0, 0), ?_⟩
  conv_lhs => rw [← hrecon, he, map_smul]
  rfl

end FiniteChains.Davis
