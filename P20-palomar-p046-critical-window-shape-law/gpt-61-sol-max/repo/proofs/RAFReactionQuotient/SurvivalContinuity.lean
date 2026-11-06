
import proofs.RAFReactionQuotient.SeedApproximation
import proofs.RAFReactionQuotient.SeedBulk
import proofs.HordijkSteelThreshold.StaticEventContinuity



namespace RAFReactionQuotient
open MeasureTheory unitInterval HordijkSteelThreshold

theorem quotientSurvival_le_finite_escape (a : I) (K : ℕ) :
    quotientSurvival a ≤ quotientStaticMeasure _ a (quotientEscapeEvent 2 K) := by
  rw [quotient_escape_measure_eq, quotientSurvival_eq]
  apply measure_mono
  intro field hf
  exact?

end RAFReactionQuotient
