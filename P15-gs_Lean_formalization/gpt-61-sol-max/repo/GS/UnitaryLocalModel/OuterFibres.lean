
import GS.UnitaryLocalModel.PauliCoordinates
import GS.Frobenius
import GS.RankOne
open GS.MatrixBase



/-!
# Exact fibres of the real three-row rank-one parametrization

These are the sphere fibres required by the unitary local model. The sign
identification and collapsed zero fibre are proved, including all degeneracies.
-/
namespace GS.UnitaryLocalModel

def sphereOuter {κ : Type*} (u : AxisVector) (z : κ → ℝ) : Matrix (Fin 3) κ ℝ := fun i j => u i * z j








/-- The sphere variable does not change the squared Frobenius radius. -/
theorem frobSq_sphereOuter {κ : Type*} [Fintype κ] {u : AxisVector}
    (hu : OnSphere u) (z : κ → ℝ) :
    cFrobSq (sphereOuter u z) = ∑ j, z j ^ 2 := RankOne.frobSq_outer (by simpa [OnSphere, Fin.sum_univ_three] using hu) z


/-- The complete fibre classification includes the collapsed zero stratum.
No choice of a nonzero coordinate is required in the statement. -/
theorem sphereOuter_fibres {κ : Type*} {u v : AxisVector} {z w : κ → ℝ}
    (hu : OnSphere u) (hv : OnSphere v) :
    sphereOuter u z = sphereOuter v w ↔
      (z = 0 ∧ w = 0) ∨ (u = v ∧ z = w) ∨ (u = -v ∧ z = -w) := RankOne.fibres (by simpa [OnSphere, Fin.sum_univ_three] using hu)
    (by simpa [OnSphere, Fin.sum_univ_three] using hv)

end GS.UnitaryLocalModel
