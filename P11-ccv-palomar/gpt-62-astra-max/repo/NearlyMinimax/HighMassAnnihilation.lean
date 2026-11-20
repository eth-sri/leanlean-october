module

public import NearlyMinimax.HighCanonicalDensityMean
public import NearlyMinimax.HistoryPatchStateAppend
public import NearlyMinimax.CenteredPacketAnnihilation

@[expose] public section

/-! Conditional signed annihilation of the actual canonical-history mass.
The canonical append identity and response-independent density reset are
proved from the constructed full-mark update. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]

end NearlyMinimax
