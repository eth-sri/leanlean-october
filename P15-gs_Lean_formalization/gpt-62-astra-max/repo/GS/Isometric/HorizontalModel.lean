module

public import GS.Isometric.Parameter
public import GS.OverlapGeometry.HorizontalModel

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Horizontal coordinates for an actual shared orbit

The complement and its continuous ambient left inverse reuse the general
finite-dimensional constructions.  The differential is the actual derivative
of the shared factor map.  The carrier P need not be unitary.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS.OverlapGeometry
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (r l : Layer 𝕜 n) (P : Square 𝕜 n)
def orbitDerivative := (pointMap r l P).toContinuousLinearMap
abbrev OrbitKernel := LinearMap.ker (orbitDerivative r l P).toLinearMap
abbrev HorizontalModel := horizontalComplement (orbitDerivative r l P)
end GS.Isometric
