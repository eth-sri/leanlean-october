module
public import MathCollab.Density.DetectorTruncation

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Fixed at each scale T: independent of both coordinates of the zero. -/
def firstDetectorCoefficient (T : ℝ) (n : ℕ) : ℂ :=
  if ⌊firstDetectorX T⌋₊ < n ∧ n < firstDetectorCutoff T then
    (mollifierCoefficient (firstDetectorX T) n : ℂ)*(Real.exp (-(n : ℝ)/T) : ℂ)
  else 0









