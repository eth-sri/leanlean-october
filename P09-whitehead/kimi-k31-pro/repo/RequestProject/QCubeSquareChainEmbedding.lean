module

public import RequestProject.QCubeSquareSupport

@[expose] public section

/-! Faithful finite square-chain subdivision, separated by actual top cubes. -/
open scoped Classical
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V C : Type} [DecidableEq V] {A : CommRel V}
  (cell : C → QCube A) (left right : C → V)
  (hne : ∀ i, left i ≠ right i) (hspx : ∀ i, (cell i).spx = {left i, right i})

noncomputable def squareChainSubdivision : (C →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ
    (fun i => cubeSquareSubdivision (cell i) (left i) (right i) (hne i) (hspx i))

theorem squareChainSubdivision_filter_top (hcell : Function.Injective cell)
    (z : C →₀ ℤ) (i : C) :
    (squareChainSubdivision cell left right hne hspx z).filter
      (fun t : (strictOrderCx (QCube A)).F => t.1.2.2 = cell i) =
      z i • cubeSquareSubdivision (cell i) (left i) (right i) (hne i) (hspx i) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp [Finsupp.filter_zero]
  | add z w hz hw =>
      rw [map_add, Finsupp.filter_add, hz, hw, Finsupp.add_apply, add_smul]
  | single j n =>
      rw [squareChainSubdivision, Finsupp.linearCombination_single,
        Finsupp.filter_smul, cubeSquareSubdivision_filter_top]
      by_cases hji : j = i
      · subst j
        simp
      · have hci : cell j ≠ cell i := fun h => hji (hcell h)
        simp [hci, hji]

end FiniteChains.Davis
