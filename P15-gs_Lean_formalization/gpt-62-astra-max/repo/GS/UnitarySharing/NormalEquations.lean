module

public import GS.UnitarySharing.MinimumNormLift

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Complete real normal equations for unitary shared factors

For D_X(A,B)=AX+XB the physical adjoint is
(proj_left(Z X*), proj_right(X* Z)). Both projections include every repeated
complex entry. All positions, including nonoverlap positions tied to overlap
coordinates, occur in these equations. Singular normal operators are allowed.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry
namespace GS.UnitarySharing
variable {n : ℕ} {right left : Pattern n}

end GS.UnitarySharing
