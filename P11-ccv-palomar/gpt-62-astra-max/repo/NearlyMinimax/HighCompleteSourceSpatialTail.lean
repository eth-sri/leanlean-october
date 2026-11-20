module

public import NearlyMinimax.HighCompleteSourceFrameTail
public import NearlyMinimax.HighMarkedMeasurable
public import NearlyMinimax.ResponseConfigurationEnergy
public import NearlyMinimax.AliasTailSummation
public import NearlyMinimax.CardinalProductDesign

@[expose] public section

/-! Genuine spatial and factorial large-count bounds for the complete
canonical source. The raw uniform cap is proved from actual packet total
variation, and all response/spatial integrations are derived here. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

theorem fullSpatialPatchDesign_real_univ (d n : ℕ) :
    (fullSpatialPatchDesign d n).real univ = (2 : ℝ)^(d*n) := by
  simp only [fullSpatialPatchDesign, measureReal_def, Measure.pi_univ,
    Measure.restrict_apply_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow]
  change (volume.real (spatialPatchBox d))^n = _
  rw [spatialPatchBox_real_volume, pow_mul]

end NearlyMinimax
