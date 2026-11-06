module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Order.Compact
public import GS.ComplexAlgebra
public import GS.Core
public import GS.Frobenius
public import GS.Unitary.Frobenius
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.Projection
public import GS.Unitary.Support
public import GS.UnitaryManifold.BlockGroup
public import GS.UnitaryManifold.CayleyAlgebra
public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.CayleyModel
public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.MatrixCalculus


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The exact real differential of the unitary Cayley reconstruction. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix Filter
open scoped Topology
namespace GS.UnitaryManifold
variable {n : ℕ} {block : Fin n → ℕ}

/-- Obtain the derivative from the identity c(A)(1+A)=1-A, rather than using
an unverified formula for differentiation of matrix inverse. -/
theorem chartInv_line_hasDerivAt_zero (Q : BlockU block) (v : Model block) :
    HasDerivAt (fun t : ℝ => chartInv Q (t • v)) ((-2 : ℝ) • (Q.val * v.val)) 0 := by
  let V := fderiv ℝ (chartInv Q) 0 v
  have hd : HasDerivAt (fun t : ℝ => chartInv Q (t • v)) V 0 := by
    have hi := ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
    exact hi.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hp : HasDerivAt (fun t : ℝ => (1 : CMat n) + t • v.val) v.val 0 := by
    simpa only [Pi.add_def, Pi.sub_def, zero_add, zero_sub, id_eq, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : CMat n)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hm : HasDerivAt (fun t : ℝ => (1 : CMat n) - t • v.val) (-v.val) 0 := by
    simpa only [Pi.add_def, Pi.sub_def, zero_add, zero_sub, id_eq, one_smul] using (hasDerivAt_const (0 : ℝ) (1 : CMat n)).sub
      ((hasDerivAt_id (0 : ℝ)).smul_const v.val)
  have hleft := hasDerivAt_matrix_mul hd hp
  have hright := hasDerivAt_matrix_mul (hasDerivAt_const (0 : ℝ) Q.val) hm
  have hid : (fun t : ℝ => chartInv Q (t • v) * (1 + t • v.val)) =
      (fun t : ℝ => Q.val * (1 - t • v.val)) := by
    funext t
    change Q.val * cayley ((t • v).val) * (1 + (t • v).val) = _
    rw [Matrix.mul_assoc, cayley_mul _ (admissible_model (t • v))]
    rfl
  rw [hid] at hleft
  have hv : V + Q.val * v.val = -(Q.val * v.val) := by
    simpa only [zero_smul, add_zero, sub_zero, chartInv_zero, Matrix.mul_one,
      Matrix.zero_mul, zero_add, Matrix.mul_neg] using hleft.unique hright
  have he : V = (-2 : ℝ) • (Q.val * v.val) := by
    have hz : V = -(Q.val * v.val) - Q.val * v.val := eq_sub_of_add_eq hv
    rw [hz, neg_smul, two_smul]
    abel
  rwa [he] at hd

end GS.UnitaryManifold
