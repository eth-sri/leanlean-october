module

public import NearlyMinimax.DesignCounts
public import NearlyMinimax.HighObservationLaw
public import NearlyMinimax.HighWindowGeometry

@[expose] public section

/-! Actual binomial occupancy under the normalized original design law,
and the exact fixed denominator constant used in the high lower score
energy. Raw normalization and patch volume are derived. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local instance] Classical.propDecidable

/-- The exact source C_sharp, obtained from one raw density floor and one
normalizing mass floor in the selected likelihood. -/
def highFixedScoreDenominator (pMinus cMass : ℝ) : ℝ := (pMinus ^ 2 * cMass)⁻¹

theorem high_fixed_score_denominator_pos {pMinus cMass : ℝ} (hp : 0 < pMinus) (hc : 0 < cMass) :
    0 < highFixedScoreDenominator pMinus cMass := by
  unfold highFixedScoreDenominator
  positivity

end NearlyMinimax
