module

public import GS.NonmanifoldClosure.DifferentiableObstruction
public import GS.RestrictedNonmanifold.SkewDimension

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Differential obstruction in the actual skew-coordinate dimensions

For every `q ≥ 3` and every finite collection of free real coordinates,
the rank-one cone on `UpperIndex q` admits no local ambient retraction
that is differentiable at zero. The two distinct columns are the actual
skew entries `(0,1)` and `(0,2)` supplied by `threeUpperIndices`.

This is an unconditional differential statement. It does not establish
the separate topological nonmanifold target, and it needs no parity condition.
The topological target is proved in `GS.NonmanifoldClosure.TopologicalClosure`.
-/

noncomputable section

open Matrix GS.Nonmanifold Filter
open scoped Topology

namespace GS.RestrictedNonmanifold

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {ι : Type*} [Fintype ι]

end GS.RestrictedNonmanifold
