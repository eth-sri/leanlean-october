module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.Order.Compact
public import GS.ComplexAlgebra
public import GS.Core
public import GS.Frobenius
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.Frobenius
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support
public import GS.UnitaryManifold.BlockGroup


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Two-sided action, its orbit, and smooth ambient matrix operations

This is an actual mathlib MulAction and ContinuousSMul, not an orbit-shaped
existential definition. ContDiff below is in ambient matrix coordinates.
It does not assert a charted-space structure on BlockU or on its orbit.

All smoothness statements use real scalar coordinates.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryManifold
open GS.UnitaryGeometry
variable {n : ℕ}

instance factorMulAction (block₁ block₂ : Fin n → ℕ) :
    MulAction (FactorGroup block₁ block₂) (CMat n) where
  smul g X := g.1.val * X * g.2.valᴴ
  one_smul X := by
    change ((1 : CMat n) * X) * (1 : CMat n)ᴴ = X
    simp
  mul_smul g h X := by
    change ((g.1.val * h.1.val) * X) * (g.2.val * h.2.val)ᴴ =
      (g.1.val * ((h.1.val * X) * h.2.valᴴ)) * g.2.valᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem action_apply {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) (X : CMat n) :
    g • X = (g.1 : CMat n) * X * (g.2 : CMat n)ᴴ := rfl

theorem action_cFrobInner {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) (X Y : CMat n) :
    cFrobInner (g • X) (g • Y) = cFrobInner X Y := by
  change cFrobInner (g.1.val * X * g.2.valᴴ)
    (g.1.val * Y * g.2.valᴴ) = _
  rw [cFrobInner_right_unitary _ g.2.property.2.conjTranspose,
    cFrobInner_left_unitary _ g.1.property.2]

/-- A fixed group element is a linear equivalence of the ambient matrix space.
No assertion about an inappropriate default matrix norm is made. -/
def actionLinearEquiv {block₁ block₂ : Fin n → ℕ}
    (g : FactorGroup block₁ block₂) : CMat n ≃ₗ[ℝ] CMat n where
  toFun X := g • X
  invFun X := g⁻¹ • X
  left_inv X := inv_smul_smul g X
  right_inv X := smul_inv_smul g X
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by simp [Matrix.mul_smul, Matrix.smul_mul]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Smooth multiplication written componentwise so it uses the ordinary
finite-product matrix norm, not an assumed operator-norm inner product. -/
theorem smooth_matrix_product {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E → CMat n} (hA : ContDiff ℝ ⊤ A) (hB : ContDiff ℝ ⊤ B) :
    ContDiff ℝ ⊤ (fun x => A x * B x) := by
  apply contDiff_pi.mpr; intro i
  apply contDiff_pi.mpr; intro j
  simp only [Matrix.mul_apply]
  apply ContDiff.sum; intro k _
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) k).mul
    (contDiff_pi.mp (contDiff_pi.mp hB k) j)

end GS.UnitaryManifold
