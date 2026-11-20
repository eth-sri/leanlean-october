module

public import QPBT.Observables.LineMeasurement.LinePointOverlap

/-! Projective refinement of evaluation classes. -/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-! ## Generic bipartite estimates -/

namespace DistanceCalculus

/-- A projective effect is absorbed by the postprocessed effect of the fiber
containing its own outcome. Formalization-only auxiliary for the projective
refinement of `fact:add-a-proj2` used by `eq:qld-comm-line-pt-cons`. -/
theorem effect_mul_postprocess_effect_self {α β ι : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement α ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M) (g : α → β) (a : α) :
    M.effect a * (M.postprocess g).effect (g a) = M.effect a := by
  simpa using SandwichProduct.effect_mul_postprocess_effect M hM g (g a) a

end DistanceCalculus

end

end MIPStarRE.QPBT
