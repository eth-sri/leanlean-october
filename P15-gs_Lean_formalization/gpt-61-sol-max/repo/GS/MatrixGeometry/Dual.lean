import GS.MatrixGeometry.Inner
noncomputable section
namespace GS.MatrixBase
variable {𝕜 : Type} [RCLike 𝕜]

variable (D : KMat 𝕜 n →L[ℝ] ℝ)

variable (f : KMat 𝕜 n → ℝ)






def dualMatrix  : KMat 𝕜 n :=
  decodeCFrob ((InnerProductSpace.toDual ℝ (CFrobCoordinates 𝕜 n)).symm
    (D.comp (decodeCFrob : CFrobCoordinates 𝕜 n →ₗ[ℝ] KMat 𝕜 n).toContinuousLinearMap))

theorem functional_eq_cFrobInner  (A : KMat 𝕜 n) :
    D A = cFrobInner (dualMatrix D) A := by
  rw [← encodeCFrob_inner]
  unfold dualMatrix
  rw [encode_decode_cFrob, InnerProductSpace.toDual_symm_apply]
  rfl



def ambientGradient  (X : KMat 𝕜 n) : KMat 𝕜 n :=
  dualMatrix (fderiv ℝ f X)


end GS.MatrixBase
