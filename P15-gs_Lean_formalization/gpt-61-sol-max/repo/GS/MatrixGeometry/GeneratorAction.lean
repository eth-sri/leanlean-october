import Mathlib.Tactic
import GS.MatrixGeometry.Base

import GS.MatrixGeometry.MinimumNormLift



/-!
# Equivariance of the minimum-physical-norm shared lift

Both spatial generators transform by unitary conjugation. This preserves
the actual tied generator spaces, their physical Frobenius pairing, and the
synthesis kernel. Uniqueness of the horizontal lift then proves equivariance
without choosing a section of the orbit map.
-/

open Matrix GS.MatrixBase
namespace GS.MatrixGeometry
variable {𝕜 : Type} [RCLike 𝕜]
variable  {right left : Pattern 𝕜 n}
variable (g : Factors right left)

variable (v w : PairGenerator right left)

variable (A C X Z : KMat 𝕜 n)

private theorem conjugate_cancel  (hA : GS.MatrixBase.Unitary A) :
    Aᴴ * (A * C * Aᴴ) * A = C := by
  calc
    _ = (Aᴴ * A) * C * (Aᴴ * A) := by noncomm_ring
    _ = _ := by rw [hA.1]; simp

@[simp] theorem generatorAction_inverse   :
    generatorAction g⁻¹ (generatorAction g v) = v := by grind [generatorAction_left,generatorAction_right,Factor.matrix_inv,Factor.matrix_unitary,conjugate_cancel,Prod.fst_inv,Prod.snd_inv,Matrix.conjTranspose_conjTranspose]

@[simp] theorem generatorAction_inverse_right   :
    generatorAction g (generatorAction g⁻¹ v) = v := by grind [generatorAction_inverse,inv_inv]

theorem generatorInner_action   :
    generatorInner (generatorAction g v) (generatorAction g w) = generatorInner v w := by
  grind [generatorInner, GS.MatrixBase.Unitary.conjTranspose, Factor.matrix_unitary, generatorAction_left, generatorAction_right, GS.MatrixBase.cFrobInner_left_unitary, GS.MatrixBase.cFrobInner_right_unitary]

theorem generatorAction_horizontal  
    (v : PairGenerator right left) (hv : IsHorizontal X v) :
    IsHorizontal (g • X) (generatorAction g v) := by
  intro k hk
  have hb : pointMap right left X (generatorAction g⁻¹ k) = 0 := by
    have he := pointMap_generatorAction g⁻¹ (g • X) k
    rw [inv_smul_smul, hk] at he
    simpa only [action_apply, Matrix.mul_zero, Matrix.zero_mul] using he
  calc
    generatorInner (generatorAction g v) k =
        generatorInner (generatorAction g v) (generatorAction g (generatorAction g⁻¹ k)) := by aesop
    _ = generatorInner v (generatorAction g⁻¹ k) := generatorInner_action g v _
    _ = 0 := hv _ hb

/-- The selected lift is independent of all choices made in its existence proof. -/
theorem minimumNormLift_equivariant   :
    minimumNormLift right left (g • X) (g • Z) =
      generatorAction g (minimumNormLift right left X Z) := by
  symm
  apply minimumNormLift_unique
  · rw [pointMap_generatorAction, minimumNormLift_synthesis, pointProjection_equivariant]
  · grind [generatorAction_horizontal,minimumNormLift_horizontal]



end GS.MatrixGeometry
