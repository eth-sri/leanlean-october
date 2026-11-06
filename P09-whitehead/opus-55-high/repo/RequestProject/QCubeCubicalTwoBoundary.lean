import RequestProject.QCubeEdgeChainEmbedding
import RequestProject.QCubeSquareFrameUniqueness
import RequestProject.Tac
noncomputable section


/-! The actual cubical edge boundary and its faithful strict subdivision. -/
namespace FiniteChains.Davis
open RACG
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

def qSquareSmallFacet (c : QSquare A) (s : ZMod 2) : QEdge A :=
  ⟨qCubeFacet c.1 (qSquareRight c) s, by
    rw [squareFacet_v_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s]
    simp⟩

def qSquareLargeFacet (c : QSquare A) (s : ZMod 2) : QEdge A :=
  ⟨qCubeFacet c.1 (qSquareLeft c) s, by
    rw [squareFacet_w_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s]
    simp⟩

def qSquareCubicalFaceBoundary (c : QSquare A) : QEdge A →₀ ℤ :=
  Finsupp.single (qSquareSmallFacet c 0) 1 - Finsupp.single (qSquareSmallFacet c 1) 1 -
    Finsupp.single (qSquareLargeFacet c 0) 1 + Finsupp.single (qSquareLargeFacet c 1) 1

def qSquareCubicalBoundary : (QSquare A →₀ ℤ) →ₗ[ℤ] (QEdge A →₀ ℤ) :=
  Finsupp.linearCombination ℤ qSquareCubicalFaceBoundary

omit [LinearOrder V] in
theorem qEdgeChainSubdivision_single (c : QEdge A) (n : ℤ) :
    qEdgeChainSubdivision (Finsupp.single c n) = n • qEdgeSubdivision c := by
  rw [qEdgeChainSubdivision, Finsupp.linearCombination_single]

theorem qEdgeSubdivision_smallFacet (c : QSquare A) s :
    qEdgeSubdivision (qSquareSmallFacet c s) =
      oneCubeSubdivision (qCubeFacet c.1 (qSquareRight c) s) (qSquareLeft c)
        (squareFacet_v_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s) :=
  qEdgeSubdivision_eq _ _ _

theorem qEdgeSubdivision_largeFacet (c : QSquare A) s :
    qEdgeSubdivision (qSquareLargeFacet c s) =
      oneCubeSubdivision (qCubeFacet c.1 (qSquareLeft c) s) (qSquareRight c)
        (squareFacet_w_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s) :=
  qEdgeSubdivision_eq _ _ _

theorem qSquareCubicalFaceBoundary_subdivision (c : QSquare A) :
    qEdgeChainSubdivision (qSquareCubicalFaceBoundary c) =
      cubeSquareEdgeBoundary c.1 (qSquareLeft c) (qSquareRight c)
        (qSquare_directions_ne c) (qSquare_free_directions c) := by
  rw [qSquareCubicalFaceBoundary, map_add, map_sub, map_sub]
  simp [qEdgeChainSubdivision_single, one_smul,
    qEdgeSubdivision_smallFacet, qEdgeSubdivision_largeFacet]
  rfl

/-- The actual cubical boundary commutes with the proved edge and square subdivisions. -/
theorem qSquareCubicalBoundary_subdivision (r : QSquare A →₀ ℤ) :
    qEdgeChainSubdivision (qSquareCubicalBoundary r) = qSquareFacetBoundary r := by
  lin_ind r c n =>
      grind [qSquareCubicalBoundary, Finsupp.linearCombination_single, map_smul, qSquareCubicalFaceBoundary_subdivision, qSquareFacetBoundary, squareChainEdgeBoundary]

/-- Faithful edge subdivision reflects the actual cubical square-cycle equations. -/
theorem qSquareCubicalBoundary_zero_iff (r : QSquare A →₀ ℤ) :
    qSquareCubicalBoundary r = 0 ↔ qSquareFacetBoundary r = 0 := by
  constructor
  · intro h
    rw [← qSquareCubicalBoundary_subdivision, h, map_zero]
  · intro h
    apply qEdgeChainSubdivision_injective
    rwa [map_zero, qSquareCubicalBoundary_subdivision]
