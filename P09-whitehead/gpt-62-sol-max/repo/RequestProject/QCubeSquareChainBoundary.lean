module

public import RequestProject.QCubeSquareChainEmbedding
public import RequestProject.FinsuppBasis

@[expose] public section

/-! Degree-two boundary naturality of the actual finite square-chain subdivision. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V C : Type} [DecidableEq V] {A : CommRel V}
  (cell : C → QCube A) (left right : C → V)
  (hne : ∀ i, left i ≠ right i) (hspx : ∀ i, (cell i).spx = {left i, right i})

noncomputable def squareChainEdgeBoundary : (C →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun i => cubeSquareEdgeBoundary (cell i) (left i) (right i) (hne i) (hspx i))

theorem squareChainSubdivision_boundary (z : C →₀ ℤ) :
    Comb.bdry2 (strictOrderCx (QCube A))
      (squareChainSubdivision cell left right hne hspx z) =
      squareChainEdgeBoundary cell left right hne hspx z := by
  finsupp_basis z
  simp [squareChainSubdivision, Finsupp.linearCombination_single, cubeSquareSubdivision_boundary, squareChainEdgeBoundary]

end FiniteChains.Davis
