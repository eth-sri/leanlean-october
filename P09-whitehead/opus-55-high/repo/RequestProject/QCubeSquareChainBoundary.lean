import RequestProject.QCubeSquareChainEmbedding
import RequestProject.Tac


/-! Degree-two boundary naturality of the actual finite square-chain subdivision. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V C : Type} [DecidableEq V] {A : CommRel V}
  (cell : C → QCube A) (left right : C → V)
  (hne : ∀ i, left i ≠ right i) (hspx : ∀ i, (cell i).spx = {left i, right i})

noncomputable def squareChainEdgeBoundary : (C →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).E →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun i => cubeSquareEdgeBoundary _ _ _ (hne i) (hspx i))

theorem squareChainSubdivision_boundary z :
    Comb.bdry2 (strictOrderCx (QCube A))
      (squareChainSubdivision cell left right hne hspx z) =
      squareChainEdgeBoundary cell left right hne hspx z := by
  lin_ind z i n =>
      grind [squareChainSubdivision, Finsupp.linearCombination_single, map_smul, cubeSquareSubdivision_boundary, squareChainEdgeBoundary]
