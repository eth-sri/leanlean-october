module

public import GS.Unitary.PointGenerators

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A polynomial extension of the intrinsic unitary tangent projector

On every two-factor unitary orbit, the previously constructed real-Frobenius
projector agrees with an explicit polynomial expression in the base matrix
and ambient direction. Its ambient extension is jointly smooth and does not
use factor representatives. Arbitrary independent overlap is allowed.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryManifold
namespace GS.UnitaryGeometry
variable {n : ℕ}

end GS.UnitaryGeometry
