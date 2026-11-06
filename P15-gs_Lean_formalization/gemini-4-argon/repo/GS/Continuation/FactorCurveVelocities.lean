module

public import GS.Continuation.ExponentialCurves
public import GS.Continuation.AmbientProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Velocities of differentiable orthogonal factor curves

We prove both directions for curves whose two factors are differentiable.
We do NOT silently assume that every differentiable curve in the image has a
local differentiable factor lift. That last assertion, or an embedded-orbit
construction, is still required to identify the image with a manifold tangent
space in the usual differential-geometric sense.
-/

noncomputable section
open Matrix
namespace GS.Continuation
open GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

end GS.Continuation
