module

public import NearlyMinimax.HighCardinalRawEnvelope
public import NearlyMinimax.FinePairSpatialEnergy

@[expose] public section

/-! Full spatial energy of the genuine matched cardinal packet numerator.
The two deterministic envelopes are integrated against the actual Q^n law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 def cardinalRawSpatialEnergyBudget d n q bd C a ρ η T  :=
  2 * cardinalRawAliasCoefficient n bd a η ^ 2 *
      ((n : ℝ)^2 * (2 : ℝ)^d * cardinalDefectSquareBudget d n T) +
    2 * cardinalRawTaylorCoefficient n q bd C a ρ η ^ 2 *
      ((n : ℝ)^2 * (2 : ℝ)^d *
        ((100*(d : ℝ))^2*16*spatialScaleIntegralConstant d)^(n-1))

end NearlyMinimax
