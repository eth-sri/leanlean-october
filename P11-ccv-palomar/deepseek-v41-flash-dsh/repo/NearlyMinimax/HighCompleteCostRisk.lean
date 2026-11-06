module

public import NearlyMinimax.HighCompletePathRisk
public import NearlyMinimax.HighPathBudget

@[expose] public section

/-! The actual complete source gives the manuscript's quantitative local
cost lower bound. The path is constructed from its true activity and
Fisher budget; positivity and variance guards are derived numerically. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable

end NearlyMinimax
