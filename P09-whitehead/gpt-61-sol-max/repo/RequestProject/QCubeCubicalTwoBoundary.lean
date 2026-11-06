import Mathlib.Tactic

import RequestProject.QCubeEdgeChainEmbedding
import RequestProject.QCubeSquareFrameUniqueness

/-! The actual cubical edge boundary and its faithful strict subdivision. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

  (c : QSquare A)
  (s : ZMod 2)
noncomputable def qSquareSmallFacet   : QEdge A :=
  ⟨qCubeFacet c.1 (qSquareRight c) s, by
    rw [squareFacet_v_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s]
    simp⟩

noncomputable def qSquareLargeFacet   : QEdge A :=
  ⟨qCubeFacet c.1 (qSquareLeft c) s, by
    grind [FiniteChains.Davis.squareFacet_w_spx, FiniteChains.Davis.qSquare_free_directions]⟩

noncomputable def qSquareCubicalFaceBoundary  : QEdge A →₀ ℤ :=
  Finsupp.single (qSquareSmallFacet c 0) 1 - Finsupp.single (qSquareSmallFacet c 1) 1 -
    Finsupp.single (qSquareLargeFacet c 0) 1 + Finsupp.single (qSquareLargeFacet c 1) 1

noncomputable def qSquareCubicalBoundary : (QSquare A →₀ ℤ) →ₗ[ℤ] (QEdge A →₀ ℤ) :=
  Finsupp.linearCombination ℤ qSquareCubicalFaceBoundary

omit [LinearOrder V] in
theorem qEdgeChainSubdivision_single (c : QEdge A) (n : ℤ) :
    qEdgeChainSubdivision (Finsupp.single c n) = n • qEdgeSubdivision c := by
  rw [qEdgeChainSubdivision, Finsupp.linearCombination_single]

theorem qEdgeSubdivision_smallFacet   :
    qEdgeSubdivision (qSquareSmallFacet c s) =
      oneCubeSubdivision (qCubeFacet c.1 (qSquareRight c) s) (qSquareLeft c)
        (squareFacet_v_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s) :=
  qEdgeSubdivision_eq _ _ _

theorem qEdgeSubdivision_largeFacet   :
    qEdgeSubdivision (qSquareLargeFacet c s) =
      oneCubeSubdivision (qCubeFacet c.1 (qSquareLeft c) s) (qSquareRight c)
        (squareFacet_w_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s) :=
  qEdgeSubdivision_eq _ _ _

theorem qSquareCubicalFaceBoundary_subdivision  :
    qEdgeChainSubdivision (qSquareCubicalFaceBoundary c) =
      cubeSquareEdgeBoundary c.1 (qSquareLeft c) (qSquareRight c)
        (qSquare_directions_ne c) (qSquare_free_directions c) := by
  aesop (add simp [qSquareCubicalFaceBoundary, qEdgeChainSubdivision_single, qEdgeSubdivision_smallFacet, qEdgeSubdivision_largeFacet])

variable (r : QSquare A →₀ ℤ)
/-- The actual cubical boundary commutes with the proved edge and square subdivisions. -/
theorem qSquareCubicalBoundary_subdivision  :
    qEdgeChainSubdivision (qSquareCubicalBoundary r) = qSquareFacetBoundary r := by
  induction r using Finsupp.induction_linear <;> simp_all [qSquareCubicalBoundary, qSquareCubicalFaceBoundary_subdivision, qSquareFacetBoundary, squareChainEdgeBoundary]

/-- Faithful edge subdivision reflects the actual cubical square-cycle equations. -/
theorem qSquareCubicalBoundary_zero_iff  :
    qSquareCubicalBoundary r = 0 ↔ qSquareFacetBoundary r = 0 := by
  constructor
  · intro h
    rw [← qSquareCubicalBoundary_subdivision, h, map_zero]
  · intro h
    apply qEdgeChainSubdivision_injective
    rwa [map_zero, qSquareCubicalBoundary_subdivision]

end FiniteChains.Davis
