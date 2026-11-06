module

public import NearlyMinimax.HighWindowGeometry
public import NearlyMinimax.HighFrameCoefficientBridge
public import NearlyMinimax.HighDensityUpdates
public import NearlyMinimax.HistoryReferenceMeasure

@[expose] public section

/-! Actual density/coefficient state maps for the high-regime marked prior. -/
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

abbrev HighRawState d k D :=
  (Covariate d → ℝ) × (HighWindowLabels d k → (HighFrameIndex d D → ℝ))

end NearlyMinimax
