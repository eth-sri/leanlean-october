module
public import QuadraticWindow
public import MathCollab.Density.Stronger.InitialDetector

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector

/-- Numeric contour-detector conditions, independent of the old polynomial
counting inequalities in QuadraticWindow. -/
structure PhysicalDetectorWindow (σ a : ℝ) : Prop where
  sigma_low : 3/4 < σ
  sigma_high : σ < 1
  a_low : 1/2 ≤ a
  a_high : a < 2/3
  threshold : 1/8 < (3*a/4)*(σ-1/2)




end Montgomery.RationalMoment.RightDetector
