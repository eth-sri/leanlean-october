module

public import RequestProject.QCubeThreeFaceEdges


@[expose] public section

/-! The indexed six-face boundary is the actual geometric cubical boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

variable (c : QThreeCube A)

theorem qThreeFace_boundary_column (i : Fin 3 × ZMod 2) :
    qSquareCubicalFaceBoundary
      (qThreeFaceSquare c i) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c) (threeFacetBoundaryColumn i) := by
  simp only [threeFacetBoundaryColumn, qSquareCubicalFaceBoundary, map_sub, map_add,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, (qThreeFaceEdges c i _).1, (qThreeFaceEdges c i _).2]

/-- Boundary naturality for every finite chain of actual indexed square facets. -/
theorem qThreeFace_boundary_naturality
    (r : (Fin 3 × ZMod 2) →₀ ℤ) :
    qSquareCubicalBoundary
      (Finsupp.lmapDomain ℤ ℤ
        (qThreeFaceSquare c) r) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c) (threeFacetBoundaryMatrix r) := by
  classical
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r z hr hz => simp_all [map_add, hr, hz]
  | single i n =>
      simp_all [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, qSquareCubicalBoundary, Finsupp.linearCombination_single, threeFacetBoundaryMatrix, map_smul, qThreeFace_boundary_column]

end FiniteChains.Davis
