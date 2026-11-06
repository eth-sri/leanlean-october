module

public import NearlyMinimax.HighSelectedScoreEnergy

@[expose] public section

/-! Exact response-configuration sums and their normalized-design transfer.
The factor `3^n` is the cardinality of the genuine ternary response space. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax

attribute [local instance] Classical.propDecidable
end NearlyMinimax
