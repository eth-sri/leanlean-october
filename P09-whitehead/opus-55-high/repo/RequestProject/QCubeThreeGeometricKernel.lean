import RequestProject.QCubeThreeBoundaryNaturality


/-! The actual cubical facet-cycle equations have the oriented rank-one kernel. -/
namespace FiniteChains.Davis
open RACG
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qThreeFace_cycle_coefficients (c : QCube A) u v w
    huv (hvw : w < v) hs
    (r : (Fin 3 × ZMod 2) →₀ ℤ)
    (hr : qSquareCubicalBoundary
      (Finsupp.lmapDomain ℤ ℤ
        (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) r) = 0) :
    ∀ i, r i = r (0, 0) * threeFacetOrientation i := by
  apply threeFacetBoundaryMatrix_kernel
  apply Finsupp.mapDomain_injective
    (qThreeEdge_injective c u v w _ _
      _ hs)
  exact (qThreeFace_boundary_naturality c u v w huv hvw hs r).symm.trans hr
