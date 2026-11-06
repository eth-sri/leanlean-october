module

public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory

def detourFailed {R Ω : Type*} (field : R → Ω → Prop) (B : Finset R) (ω : Ω) : Prop :=
  ¬ ∀ r ∈ B, field r ω

end HordijkSteelThreshold
