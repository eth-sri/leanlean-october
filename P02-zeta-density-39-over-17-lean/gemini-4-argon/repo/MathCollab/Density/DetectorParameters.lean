module
public import MathCollab.Density.ZeroLargeValues
public import MathCollab.Density.MollifierCoefficients

@[expose] public section

open Filter
open scoped Topology

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- The first density target's cutoff, distinct from other detector choices. -/
def firstDetectorX (T : ℝ) : ℝ := 2*T^(1/8 : ℝ)




