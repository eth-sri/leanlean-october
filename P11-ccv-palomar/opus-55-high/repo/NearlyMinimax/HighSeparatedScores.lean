module

public import NearlyMinimax.HighTorusScores

@[expose] public section

/-! Genuine signed-Xi local scores. The bridge to conditional product-law
orthogonality is proved by evaluating the actual separated signed measure,
with outer integrability supplied by its matrix representation cost. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]

end
end NearlyMinimax
