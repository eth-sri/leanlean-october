module
import Mathlib
public import MathCollab.Density.DetectorTruncation

@[expose] public section

open Complex MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
namespace MathCollab.Density

/- Fixed at each scale T: independent of both coordinates of the zero. -/
def firstDetectorCoefficient (T : ℝ) (n : ℕ) : ℂ :=
  if ⌊firstDetectorX T⌋₊ < n ∧ n < firstDetectorCutoff T then
    (mollifierCoefficient (firstDetectorX T) n : ℂ)*(Real.exp (-(n : ℝ)/T) : ℂ)
  else 0



section
variable {T : ℝ}
include T












end





