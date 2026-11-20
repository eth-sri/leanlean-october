module

public import RequestProject.QCubeThreeBoundaryNaturality

@[expose] public section

/-! The actual cubical facet-cycle equations have the oriented rank-one kernel. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qThreeFace_cycle_coefficients (c : QThreeCube A)
    (r : (Fin 3 × ZMod 2) →₀ ℤ)
    (hr : qSquareCubicalBoundary
      (Finsupp.lmapDomain ℤ ℤ
        (qThreeFaceSquare c) r) = 0) :
    ∀ i, r i = r (0, 0) * threeFacetOrientation i := by
  apply threeFacetBoundaryMatrix_kernel
  apply Finsupp.mapDomain_injective
    (qThreeEdge_injective c)
  exact (qThreeFace_boundary_naturality c r).symm.trans hr

end FiniteChains.Davis
