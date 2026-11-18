module

public import GS.SharedGeodesics.Orthogonal
public import GS.SharedGeometry.GeneratorAction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Factor-independent orthogonal shared geodesics

First prove intertwining for the convergent matrix power series. Under
nonoverlap, the actual point synthesis is an isometry for the physical
(expanded-block) generator norm and hence injective. The spatial exponential
word then proves independence from both the factor representative and the
compatible initial generators. No uniqueness theorem for an assumed ODE is used.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry GS.SharedGeometry
open scoped Topology BigOperators Manifold
namespace GS.SharedGeodesics
variable {n : ℕ}

variable {right left : Pattern n} (σ : Equiv.Perm (Fin n))

end GS.SharedGeodesics
