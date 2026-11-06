
import GS.GlobalGeometry.SharedAlgebra
import GS.GlobalGeometry.SharedNormalEquations
import GS.Continuation.FactorCurveVelocities



/-!
# Actual curves and feasible exponential updates with tied blocks

For full physical blocks (`0 < b` and `b ∣ n`), equal local block entries
are preserved by products, transposes and the matrix exponential.  Consequently
all shared generator directions are realized by differentiable curves of
actual tied orthogonal factors, and every differentiable factor curve has one
of these directions.

This identifies velocities of differentiable factor curves, rather than
assuming that every curve in the image admits a differentiable factor lift.
No smooth manifold assertion for an arbitrary shared image is made here.
-/

open GS.Continuation
namespace GS.GlobalGeometry

/-- An actual finite matrix factor with the specified physical block ties. -/
def SharedOrthogonalFactor (b : ℕ) (τ : ℕ → ℕ) (A : Mat n) : Prop :=
  BlockDiagonal b A ∧ Orthogonal A ∧ TiedEntries b τ A

theorem expLine_shared {n b : ℕ} {τ : ℕ → ℕ} {C : Mat n}
    (hb : 0 < b) (hbn : b ∣ n) (hC : C ∈ GS.MatrixGeometry.sharedSkewSpace b τ) (t : ℝ) :
    SharedOrthogonalFactor b τ (expLine C t) := by
  let S := (GS.MatrixGeometry.sharedMatrixSpace (𝕜 := ℝ) (n := n) b τ).toSubalgebra
    (GS.MatrixGeometry.one_mem_sharedMatrixSpace b τ)
    (fun _ _ => GS.MatrixGeometry.mul_mem_sharedMatrixSpace hb hbn)
  have hm : expLine C t ∈ S := NormedSpace.exp_mem (s := S) S.toSubmodule.closed_of_finiteDimensional
      (S.smul_mem (⟨hC.1,hC.2.2⟩ : C ∈ S) t)
  exact ⟨hm.1,matrixExp_orthogonal (isSkew_smul t hC.2.1),hm.2⟩
end GS.GlobalGeometry
