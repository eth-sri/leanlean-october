module

public import GS.UnitaryManifold.KernelCayley
public import GS.UnitaryManifold.HorizontalModel
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.OverlapGeometry Filter Set
open scoped Topology Manifold

namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}

theorem chartInv_fderiv_zero (Q : BlockU block) (v : Model block) :
    fderiv ℝ (chartInv Q) 0 v = (-2 : ℝ) • (Q.val * v.val) := by
  have hi := ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  exact (hi.comp_hasDerivAt_of_eq 0 hl (by simp)).unique
    (chartInv_line_hasDerivAt_zero Q v)

end GS.UnitaryManifold
