module

public import RequestProject.QCubeEdgeChainEmbedding
public import RequestProject.QCubeSquareFrameUniqueness

@[expose] public section

/-! The actual cubical edge boundary and its faithful strict subdivision. -/
noncomputable section

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

variable (c : QSquare A)

variable (s : ZMod 2)

def qSquareSmallFacet : QEdge A :=
  ⟨qCubeFacet c.1 (qSquareRight c) s, by
    rw [squareFacet_v_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s] <;> rfl⟩

def qSquareLargeFacet : QEdge A :=
  ⟨qCubeFacet c.1 (qSquareLeft c) s, by
    grind [squareFacet_w_spx, qSquare_directions_ne, qSquare_free_directions]⟩

def qSquareCubicalFaceBoundary : QEdge A →₀ ℤ :=
  Finsupp.single (qSquareSmallFacet c 0) 1 - Finsupp.single (qSquareSmallFacet c 1) 1 -
    Finsupp.single (qSquareLargeFacet c 0) 1 + Finsupp.single (qSquareLargeFacet c 1) 1

def qSquareCubicalBoundary : (QSquare A →₀ ℤ) →ₗ[ℤ] (QEdge A →₀ ℤ) :=
  Finsupp.linearCombination ℤ qSquareCubicalFaceBoundary

omit [LinearOrder V] in
theorem qEdgeChainSubdivision_single (c : QEdge A) (n : ℤ) :
    qEdgeChainSubdivision (Finsupp.single c n) = n • qEdgeSubdivision c := by
  rw [qEdgeChainSubdivision, Finsupp.linearCombination_single]

variable (c : QSquare A)

variable (s : ZMod 2)

theorem qEdgeSubdivision_smallFacet :
    qEdgeSubdivision (qSquareSmallFacet c s) =
      oneCubeSubdivision _ _
        (squareFacet_v_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s) :=
  by apply qEdgeSubdivision_eq

theorem qEdgeSubdivision_largeFacet :
    qEdgeSubdivision (qSquareLargeFacet c s) =
      oneCubeSubdivision _ _
        (squareFacet_w_spx c.1 (qSquare_directions_ne c) (qSquare_free_directions c) s) :=
  by apply qEdgeSubdivision_eq

theorem qSquareCubicalFaceBoundary_subdivision :
    qEdgeChainSubdivision (qSquareCubicalFaceBoundary c) =
      cubeSquareEdgeBoundary c.1 _ _
        (qSquare_directions_ne c) (qSquare_free_directions c) := by
  rw [qSquareCubicalFaceBoundary, map_add, map_sub, map_sub]
  simp only [qEdgeChainSubdivision_single, one_smul,
    qEdgeSubdivision_smallFacet, qEdgeSubdivision_largeFacet]
  rfl

variable (r : QSquare A →₀ ℤ)

/-- The actual cubical boundary commutes with the proved edge and square subdivisions. -/
theorem qSquareCubicalBoundary_subdivision :
    qEdgeChainSubdivision (qSquareCubicalBoundary r) = qSquareFacetBoundary r := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp_all
  | single c n =>
      simp [qSquareCubicalBoundary, Finsupp.linearCombination_single, map_smul, qSquareCubicalFaceBoundary_subdivision, qSquareFacetBoundary, squareChainEdgeBoundary]

/-- Faithful edge subdivision reflects the actual cubical square-cycle equations. -/
theorem qSquareCubicalBoundary_zero_iff :
    qSquareCubicalBoundary r = 0 ↔ qSquareFacetBoundary r = 0 := by
  constructor
  · intro h
    rw [← qSquareCubicalBoundary_subdivision, h, map_zero]
  · intro h
    apply qEdgeChainSubdivision_injective
    rwa [map_zero, qSquareCubicalBoundary_subdivision]

end FiniteChains.Davis
