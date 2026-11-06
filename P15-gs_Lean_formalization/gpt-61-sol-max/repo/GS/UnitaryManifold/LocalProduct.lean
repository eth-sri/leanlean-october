
import GS.UnitaryManifold.KernelCayley
import GS.UnitaryManifold.HorizontalModel
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff


set_option backward.isDefEq.respectTransparency false
/-!
# Local horizontal--stabilizer factorization

Multiplication of two factor Cayley lifts has derivative addition at the
identity. Restricting the two inputs to complementary horizontal and kernel
subspaces therefore gives a genuine local inverse-function chart.
-/

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GS.UnitaryManifold
variable  {block : Fin n → ℕ}

theorem chartInv_fderiv_zero (Q : BlockU block) (v : Model block) :
    fderiv ℝ (chartInv Q) 0 v = (-2 : ℝ) • (Q.val * v.val) := by
  have hi := ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt
  have hl  := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hi.comp_hasDerivAt_of_eq 0 hl (by simp)).unique
    (GS.MatrixBase.chartInv_line_hasDerivAt_zero Q.val v.val v.property.2)









































end GS.UnitaryManifold
