module

public import NearlyMinimax.FinePairCountTwoEnergy
public import NearlyMinimax.FinePairAliasSpatialEnergy

@[expose] public section

/-! Actual spatial energy of the complete three-row count-two numerator,
including the single heat correction and the true radial defect. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

 def finePairCountTwoSpatialBudget (d : ℕ) (bd a ρ η N : ℝ) : ℝ :=
  (η^2*bd^2*((2*ρ+a)/a^2)^2)^2 * (6*(2 : ℝ)^d*spatialExponentialConstant d/N^d)

end NearlyMinimax
