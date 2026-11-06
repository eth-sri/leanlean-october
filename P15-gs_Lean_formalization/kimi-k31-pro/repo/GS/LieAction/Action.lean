module

public import GS.LieAction.BlockGroup
public import GS.Frobenius
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

noncomputable section
open Matrix
namespace GS.LieAction
variable {n : ℕ}

instance factorMulAction (block₁ block₂ : Fin n → ℕ) :
    MulAction (FactorGroup block₁ block₂) (Mat n) where
  smul g X := g.1.val * X * g.2.valᵀ
  one_smul X := by
    change ((1 : Mat n) * X) * (1 : Mat n)ᵀ = X
    simp
  mul_smul g h X := by
    change ((g.1.val * h.1.val) * X) * (g.2.val * h.2.val)ᵀ =
      (g.1.val * ((h.1.val * X) * h.2.valᵀ)) * g.2.valᵀ
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem action_frobInner {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) (X Y : Mat n) :
    frobInner (g • X) (g • Y) = frobInner X Y := by
  change frobInner (g.1.val * X * g.2.valᵀ)
    (g.1.val * Y * g.2.valᵀ) = _
  rw [frobInner_right_orthogonal _ g.2.property.2.transpose,
    frobInner_left_orthogonal _ g.1.property.2]

/-- A fixed group element is a linear equivalence of the ambient matrix space. -/
def actionLinearEquiv {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) : Mat n ≃ₗ[ℝ] Mat n where
  toFun X := g • X
  invFun X := g⁻¹ • X
  left_inv X := inv_smul_smul g X
  right_inv X := smul_inv_smul g X
  map_add' X Y := by
    change g.1.val * (X + Y) * g.2.valᵀ = g.1.val * X * g.2.valᵀ + g.1.val * Y * g.2.valᵀ
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by
    change g.1.val * (a • X) * g.2.valᵀ = a • (g.1.val * X * g.2.valᵀ)
    simp [Matrix.mul_smul, Matrix.smul_mul]

end GS.LieAction
