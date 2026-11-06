import RequestProject.QCubeSquareFlagIndex
import RequestProject.Tac


/-! Actual coefficients of the square fundamental subdivision in its faithful flag index. -/
bwd

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def squareFlagSign (i : Bool × ZMod 2 × Bool) :=
  (if i.1 then -1 else 1) * (if i.2.1 = 0 then 1 else -1) *
    (if i.2.2 then -1 else 1)

theorem squareSubdivision_flag_coefficient (c : QCube A) a b hne
    hs i :
    cubeSquareSubdivision c a b hne hs (squareFlag c a b hne hs i) = squareFlagSign i := by
  rw [← squareFlagCoordinates_apply, squareFlagCoordinates_subdivision]
  classical
  obtain ⟨e, s, f⟩ := i
  cases e <;> fin_cases s <;> cases f <;>
    norm_num [squareFlagSign, Finsupp.single_apply, Prod.mk.injEq]
