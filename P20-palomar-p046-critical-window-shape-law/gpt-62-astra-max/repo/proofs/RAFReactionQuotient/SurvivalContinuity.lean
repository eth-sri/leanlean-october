module

public import proofs.RAFReactionQuotient.SeedApproximation
public import proofs.RAFReactionQuotient.EventContinuity

@[expose] public section

namespace RAFReactionQuotient
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval HordijkSteelThreshold
open scoped ENNReal Topology

theorem quotientSurvival_le_finite_escape (a : I) (K : ℕ) :
    quotientSurvival a ≤ quotientStaticMeasure (2*(K+2)) a (quotientEscapeEvent 2 K) := by
  rw [quotient_escape_measure_eq, quotientSurvival_eq]
  apply measure_mono
  intro field hf
  exact (reversibleEscapeEvent_iff 2 K field).mpr (hf (K+2))

end RAFReactionQuotient
