module

public import GS.UnitaryManifold.KernelCayley
public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.Action
public import GS.CompactFibres
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.Group.Quotient
public import GS.Unitary.Permutations
public import GS.UnitaryManifold.CayleyDifferential
public import GS.UnitaryManifold.MatrixCalculus
public import GS.OverlapGeometry.HorizontalModel
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ} {block : Fin n → ℕ}

theorem chartInv_fderiv_zero (Q : KBlockU 𝕂 block) (v : KModel 𝕂 block) :
    fderiv ℝ (chartInv Q) 0 v = (-2 : ℝ) • (Q.val * v.val) :=
  ((((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt).comp_hasDerivAt_of_eq 0
    (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)).unique
    (chartInv_line_hasDerivAt_zero Q v)

end GS.UnitaryManifold
