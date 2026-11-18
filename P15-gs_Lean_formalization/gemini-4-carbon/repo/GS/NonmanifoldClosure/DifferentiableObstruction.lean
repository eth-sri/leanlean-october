module

public import GS.Nonmanifold.RankOneGeometry
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# An independent differential obstruction, without sphere homology

At the vertex, the set of velocities of differentiable curves in the rank-one
cone is exactly the cone itself and is not closed under addition. Consequently
there is no local ambient retraction to the cone product differentiable at zero.

This is NOT a replacement for the topological NonManifoldGoal. It is a separate
unconditional differential statement. The implication from general embedded
submanifold machinery is not asserted here without its own formalization.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry GS.Nonmanifold Filter
open scoped Topology
namespace GS.NonmanifoldClosure

-- Use the coordinate sup norm, whose topology is the existing matrix product
-- topology; mathlib deliberately does not install a global matrix norm.
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

variable {ι : Type*} [Fintype ι]

end GS.NonmanifoldClosure
