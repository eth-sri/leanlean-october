module

public import GS.UnitaryManifold.BlockGroup
public import GS.Unitary.Frobenius
public import GS.Unitary.Factorization
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix GS.UnitaryGeometry
open scoped BigOperators
namespace GS.UnitaryManifold
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

instance factorMulAction (block₁ block₂ : Fin n → ℕ) :
    MulAction (KFactorGroup 𝕂 block₁ block₂) (Matrix (Fin n) (Fin n) 𝕂) where
  smul g X := g.1.val * X * g.2.valᴴ
  one_smul X := by change ((1 : Matrix (Fin n) (Fin n) 𝕂) * X) * (1 : Matrix (Fin n) (Fin n) 𝕂)ᴴ = X; simp
  mul_smul g h X := by
    change ((g.1.val * h.1.val) * X) * (g.2.val * h.2.val)ᴴ =
      (g.1.val * ((h.1.val * X) * h.2.valᴴ)) * g.2.valᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply {block₁ block₂ : Fin n → ℕ}
    (g : KFactorGroup 𝕂 block₁ block₂) (X : Matrix (Fin n) (Fin n) 𝕂) :
    g • X = g.1.val * X * g.2.valᴴ := rfl

theorem action_cFrobInner {block₁ block₂ : Fin n → ℕ}
    (g : KFactorGroup 𝕂 block₁ block₂) (X Y : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner (g • X) (g • Y) = cFrobInner X Y := by
  change cFrobInner (g.1.val * X * g.2.valᴴ) (g.1.val * Y * g.2.valᴴ) = _
  rw [cFrobInner_right_unitary _ g.2.property.2.conjTranspose,
    cFrobInner_left_unitary _ g.1.property.2]

def actionLinearEquiv {block₁ block₂ : Fin n → ℕ}
    (g : KFactorGroup 𝕂 block₁ block₂) :
    Matrix (Fin n) (Fin n) 𝕂 ≃ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕂 where
  toFun X := g • X
  invFun X := g⁻¹ • X
  left_inv X := inv_smul_smul g X
  right_inv X := smul_inv_smul g X
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by simp [Matrix.mul_smul, Matrix.smul_mul]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smooth_matrix_product {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E → Matrix (Fin n) (Fin n) 𝕂} (hA : ContDiff ℝ ⊤ A) (hB : ContDiff ℝ ⊤ B) :
    ContDiff ℝ ⊤ (fun x => A x * B x) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ =>
    (contDiff_pi.mp (contDiff_pi.mp hA i) k).mul (contDiff_pi.mp (contDiff_pi.mp hB k) j)

end GS.UnitaryManifold
