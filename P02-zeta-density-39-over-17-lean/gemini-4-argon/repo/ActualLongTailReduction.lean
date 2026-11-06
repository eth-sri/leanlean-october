module
public import RetunedDetectorParameters
public import MathCollab.Density.Stronger.LongScalarBudget

@[expose] public section

open Real
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger

def criticalMeanThreshold (C σ a δ T : ℝ) : ℝ :=
  (detectorY a T)^((σ-1/2)/2)/(48*C*Real.sqrt (detectorX δ T)*Real.log T)

