module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
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
public import Mathlib.Topology.Order.Compact
public import GS.CayleyCharts.Algebra
public import GS.CayleyCharts.Model
public import GS.CayleyCharts.Smooth
public import GS.Core
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.LieAction.BlockGroup
public import GS.Projection


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Explicit open charts on the existing `GS.LieAction.BlockO`

No topology is transferred to BlockO. Both sets below use the original subtype
topology. The coordinate target is an OPEN subset of a finite-dimensional real
vector space, not the variety defined by orthogonality equations.

The atlas ingredients are given by actual `Homeomorph`s and `ContDiffAt`
theorems. The mathlib ChartedSpace/IsManifold structures built from these charts are
installed in `GS.CayleyCharts.Atlas`.

-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.LieAction
namespace GS.CayleyCharts
variable {n : ℕ} {block : Fin n → ℕ}

def parameterDomain (block : Fin n → ℕ) : Set (Model block) :=
  {x | admissible x.val}

/-- Reconstruction is an actual rational matrix formula. -/
def chartInv (Q : BlockO block) (x : Model block) : Mat n :=
  Q.val * cayley x.val

@[simp] theorem chartInv_zero (Q : BlockO block) : chartInv Q 0 = Q.val := by
  simp [chartInv]

theorem chartInv_smooth_at (Q : BlockO block) (x : Model block)
    (hx : x ∈ parameterDomain block) : ContDiffAt ℝ ⊤ (chartInv Q) x :=
  smooth_mul_at contDiffAt_const
    (smooth_cayley_comp_at (modelInclusion block).contDiff.contDiffAt hx)

/-- Reconstruction is smooth on the entire finite-dimensional coordinate space. -/
theorem chartInv_smooth (Q : BlockO block) : ContDiff ℝ ⊤ (chartInv Q) := by
  exact contDiff_iff_contDiffAt.mpr (fun x => chartInv_smooth_at Q x (admissible_model x))

end GS.CayleyCharts
