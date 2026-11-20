module

public import RequestProject.QCubeThreeFaceEdges
public import RequestProject.FinsuppBasis
public import RequestProject.CubicalThreeBoundaryMatrix

@[expose] public section

/-! The indexed six-face boundary is the actual geometric cubical boundary. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qThreeFace_boundary_column (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (i : Fin 3 × ZMod 2) :
    qSquareCubicalFaceBoundary
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs i) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) (threeFacetBoundaryColumn i) := by
  classical
  obtain ⟨e, s⟩ := i
  fin_cases e <;>
    norm_num only [threeFacetBoundaryColumn, Fin.mk_eq_zero, Fin.mk_eq_one, ite_true, ite_false] <;>
    simp only [map_add, map_sub, map_neg, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      qSquareCubicalFaceBoundary, qThreeFaceSquare_small c u v w huv hvw hs,
      qThreeFaceSquare_large c u v w huv hvw hs] <;> abel!

/-- Boundary naturality for every finite chain of actual indexed square facets. -/
theorem qThreeFace_boundary_naturality (c : QCube A) (u v w : V)
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w})
    (r : (Fin 3 × ZMod 2) →₀ ℤ) :
    qSquareCubicalBoundary
      (Finsupp.lmapDomain ℤ ℤ
        (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) r) =
      Finsupp.lmapDomain ℤ ℤ
        (qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
          (Ne.symm hvw.ne) hs) (threeFacetBoundaryMatrix r) := by
  classical
  finsupp_basis r
  intro i
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    qSquareCubicalBoundary, Finsupp.linearCombination_single,
    threeFacetBoundaryMatrix, Finsupp.linearCombination_single, map_smul,
    qThreeFace_boundary_column c u v w huv hvw hs i]

end FiniteChains.Davis
