module

public import GS.Unitary.TracelessProjection
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Real-linear projection formulas are continuous and real analytic in the
ambient finite-dimensional matrix topology. This does not install a Frobenius
norm on the matrix type or assert a quotient manifold construction. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.UnitaryGeometry
variable {n : ℕ}

end GS.UnitaryGeometry
