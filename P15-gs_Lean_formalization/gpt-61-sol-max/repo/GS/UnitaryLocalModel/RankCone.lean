
import GS.UnitaryLocalModel.OuterFibres
import GS.GlobalGeometry.OriginalGImage



/-!
# The actual three-row determinantal cone

The Pauli-sphere outer map has image exactly the matrices of real rank at most
one. The result includes the zero matrix and uses mathlib's matrix rank.
-/
namespace GS.UnitaryLocalModel

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem rank_sphereOuter_le_one (u : AxisVector) (z : κ → ℝ) :
    Matrix.rank (sphereOuter u z) ≤ 1 := Matrix.rank_vecMulVec_le _ _





theorem exists_sphereOuter_of_rank_le_one (W : Matrix (Fin 3) κ ℝ)
    (hW : W.rank ≤ 1) :
    ∃ u : AxisVector, OnSphere u ∧ ∃ z : κ → ℝ, sphereOuter u z = W := by
  obtain ⟨u,hu,z,h⟩ := RankOne.exists_unit_outer (0 : Fin 3) W hW
  exact ⟨u,by simpa [OnSphere, Fin.sum_univ_three] using hu,z,h⟩


end GS.UnitaryLocalModel
