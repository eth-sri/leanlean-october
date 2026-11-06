
import proofs.HordijkSteelThreshold.ReversibleEscapeProbability
import proofs.HordijkSteelThreshold.FixedPoolReactionLaw




namespace HordijkSteelThreshold
open MeasureTheory RAF.Polymer RAF.Concrete unitInterval

theorem static_capped_escape_le (N K : ℕ) (a : I) :
    staticReactionMeasure N a {ω | ∃ x ∈ temporaryReactionClosure 2
      (staticOpenReactions ω), K+2 < molLength x} ≤
      infiniteStaticMeasure a (reversibleEscapeEvent 2 K) := by
  rw [← infiniteStatic_restriction_map N a, Measure.map_apply]
  · apply measure_mono
    intro field h
    
    obtain ⟨x,hx,hl⟩ := h
    apply (reversibleEscapeEvent_iff 2 K field).mpr
    exact ⟨moleculeWord x, by simpa [moleculeWord_length] using hl,
      finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible field x hx)⟩
  · apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact MeasurableSet.of_discrete



end HordijkSteelThreshold
