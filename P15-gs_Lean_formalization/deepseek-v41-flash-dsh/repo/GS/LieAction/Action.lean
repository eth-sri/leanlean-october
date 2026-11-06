module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
public import GS.Core
public import GS.Frobenius
public import GS.LieAction.BlockGroup


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Two-sided action, its orbit, and smooth ambient matrix operations

This is an actual mathlib MulAction and ContinuousSMul, not an orbit-shaped
existential definition. ContDiff below is in ambient matrix coordinates.
It does not assert a charted-space structure on BlockO or on its orbit.

-/

noncomputable section
open Matrix
open scoped BigOperators
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

@[simp] theorem action_apply {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) (X : Mat n) :
    g • X = (g.1 : Mat n) * X * (g.2 : Mat n)ᵀ := rfl

theorem action_frobInner {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) (X Y : Mat n) :
    frobInner (g • X) (g • Y) = frobInner X Y := by
  change frobInner (g.1.val * X * g.2.valᵀ)
    (g.1.val * Y * g.2.valᵀ) = _
  rw [frobInner_right_orthogonal _ g.2.property.2.transpose,
    frobInner_left_orthogonal _ g.1.property.2]

/-- A fixed group element is a linear equivalence of the ambient matrix space.
No assertion about an inappropriate default matrix norm is made. -/
def actionLinearEquiv {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) : Mat n ≃ₗ[ℝ] Mat n where
  toFun X := g • X
  invFun X := g⁻¹ • X
  left_inv X := inv_smul_smul g X
  right_inv X := smul_inv_smul g X
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by simp [Matrix.mul_smul, Matrix.smul_mul]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end GS.LieAction
