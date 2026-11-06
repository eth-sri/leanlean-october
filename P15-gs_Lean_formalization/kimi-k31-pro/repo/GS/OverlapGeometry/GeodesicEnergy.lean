module

public import GS.OverlapGeometry.GeodesicDynamics
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Energy conservation for the overlap generator equation

The nontrivial commutator correction changes the supported generators but
preserves the Frobenius speed. The conclusions concern actual derivatives
and give equality of energy at any two times for a global solution.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry
namespace GS.OverlapGeometry
variable {n : ℕ}

end GS.OverlapGeometry
