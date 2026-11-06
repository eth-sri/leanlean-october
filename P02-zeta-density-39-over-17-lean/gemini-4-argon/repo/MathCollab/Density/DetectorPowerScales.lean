module
public import MathCollab.Density.FixedDetectorCover

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density


def densityAmbient (T : ℝ) : ℝ := 32*T*(Real.log T)^2





