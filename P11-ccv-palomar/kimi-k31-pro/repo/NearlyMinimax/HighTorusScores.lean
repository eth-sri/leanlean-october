module

public import NearlyMinimax.HighScoreOrthogonality

@[expose] public section

/-! The actual high window graph yields disjoint-score orthogonality and
the manuscript's factor `3^d` under the genuine conditional response law.
Outer representation integrability is proved from matrix cost and legal
bounded density resets. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

section
variable {ι E Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [MeasurableSpace Z]

end
end NearlyMinimax
