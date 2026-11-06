module

public import proofs.RAFReactionQuotient.SourceBounds
public import proofs.HordijkSteelThreshold.StaticEventContinuity

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical MeasureTheory unitInterval HordijkSteelThreshold RAF.Polymer
open OverlapCorrectedRAF.Source

instance quotientCatalytic_probability (n : ℕ) (p : I) :
    IsProbabilityMeasure (quotientCatalyticLaw n p) := by
  unfold quotientCatalyticLaw
  infer_instance

end RAFReactionQuotient
