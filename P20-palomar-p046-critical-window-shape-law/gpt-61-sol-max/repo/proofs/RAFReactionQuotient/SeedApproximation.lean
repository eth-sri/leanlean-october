
import proofs.RAFReactionQuotient.FiniteApproximation
import proofs.HordijkSteelThreshold.SourceTerminalRAF
import proofs.HordijkSteelThreshold.StaticSeedMassBound




namespace RAFReactionQuotient
open MeasureTheory unitInterval HordijkSteelThreshold
open RAF.Concrete


theorem quotient_capped_escape_le (N K : ℕ) (a : I) :
    quotientStaticMeasure N a {q | ∃ x ∈ quotientClosure N 2 (quotientOpen q), K+2 < molLength x} ≤
      quotientInfiniteMeasure a (reversibleEscapeEvent 2 K) := by
  rw [← infinite_quotient_restriction_map N a,
    Measure.map_apply (Measurable.of_eval fun j => measurable_pi_apply _)
      (Set.toFinite _).measurableSet,
    quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
      (measurableSet_reversibleEscapeEvent 2 K)]
  apply measure_mono
  intro ω h
  change ∃ x ∈ quotientClosure N 2 (quotientOpen fun j => ω (quotientCoordinate j)),
    K+2 < molLength x at h
  rw [quotientClosure_restriction] at h
  obtain ⟨x,hx,hl⟩ := h
  apply (reversibleEscapeEvent_iff 2 K (quotientField ω)).mpr
  exact ⟨moleculeWord x,by simpa [moleculeWord_length] using hl,
    finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible _ x hx)⟩

end RAFReactionQuotient
