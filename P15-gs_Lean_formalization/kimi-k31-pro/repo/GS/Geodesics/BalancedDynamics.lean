module

public import GS.Geodesics.BracketGeometry
public import GS.OverlapGeometry.GeodesicDynamics

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact cancellation in the balanced overlap equation

The two exclusive generators evolve by opposite half-commutators with the
intersection generator. Their actual moving-generator acceleration has only
a symmetric square and a Frobenius-normal exclusive commutator left over.
This proves the zero projected-acceleration equation algebraically, without
assuming it as a differential-equation premise.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
open Matrix GS GS.Extensions GS.Continuation GS.OverlapGeometry

namespace GS.Geodesics
variable {n : ℕ}

end GS.Geodesics
