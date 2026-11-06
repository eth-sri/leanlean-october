module

public import NearlyMinimax.HigherBandRawCollapse
public import NearlyMinimax.HighSourceHigherCounts

@[expose] public section

/-! The complete physical source, with its single heat correction, is
exactly the matched cardinal defect plus the genuine exterior aliases
and the fine-field action.  This also covers positive target scales
below one: their actual scale domain and covariance matrix are empty. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
attribute [local instance] Classical.propDecidable

end NearlyMinimax
