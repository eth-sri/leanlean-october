module

public import GS.UnitaryNonmanifold.ExplicitCurves
public import GS.UnitaryNonmanifold.ScalarBridge
public import GS.UnitaryNonmanifold.RetractionObstruction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A certified smoothness counterexample for three unitary GS factors

For the original six-by-six scalar-shuffle family with block sizes 2,3,2,
two feasible smooth curves have velocities whose sum cannot be the velocity
of any differentiable feasible curve. Consequently the set admits neither
a local differentiable ambient retraction nor an embedded differentiable
flattening chart at the displayed rational base point.

This is a smooth embedded-submanifold obstruction. No claim of topological
nonmanifoldness is made for the complex family.
-/

noncomputable section
open Matrix Filter GS.UnitaryGeometry
open scoped Topology
namespace GS.UnitaryNonmanifold
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

@[simp] theorem cBlock_add {q : ℕ} (A B : CMat (q*2)) (i j : Fin q) :
    cBlock (A+B) i j = cBlock A i j + cBlock B i j := rfl

end GS.UnitaryNonmanifold
