module

public import proofs.RAFReactionQuotient.FiniteApproximation
public import proofs.HordijkSteelThreshold.SourceTerminalRAF
public import proofs.HordijkSteelThreshold.StaticSeedMassBound

@[expose] public section

namespace RAFReactionQuotient
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

theorem quotient_same_field_seed_mass (N L m : ℕ) (a : I) :
    quotientStaticMeasure N a {q | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ quotientClosure N 2 (quotientOpen q), moleculeWord x = w} ≤
    quotientStaticMeasure N a {q | (m-1)*Fintype.card (Molecule N) ≤
      m*(quotientClosure N 2 (quotientOpen q)).card} +
    quotientStaticMeasure N a {q | m*(quotientClosure N L (quotientOpen q)).card <
      (m-1)*Fintype.card (Molecule N)} := by
  simp_rw [quotientClosure_pullback]
  exact seed_mass_union_bound _ N L m _ _ fun _ => binaryFood_subset_of_words

theorem quotient_capped_escape_le (N K : ℕ) (a : I) :
    quotientStaticMeasure N a {q | ∃ x ∈ quotientClosure N 2 (quotientOpen q), K+2 < molLength x} ≤
      quotientInfiniteMeasure a (reversibleEscapeEvent 2 K) := by
  rw [← infinite_quotient_restriction_map N a,
    Measure.map_apply (Measurable.of_eval (fun j => measurable_pi_apply _))
      (Set.toFinite _).measurableSet,
    quotientInfiniteMeasure, Measure.map_apply quotientField_measurable
      (measurableSet_reversibleEscapeEvent 2 K)]
  refine measure_mono fun ω h => ?_
  change ∃ x ∈ quotientClosure N 2 (quotientOpen (fun j => ω (quotientCoordinate j))), K+2 < molLength x at h
  rw [quotientClosure_restriction] at h
  obtain ⟨x, hx, hl⟩ := h
  exact (reversibleEscapeEvent_iff 2 K (quotientField ω)).mpr
    ⟨moleculeWord x, by simpa only [moleculeWord_length] using hl,
      finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible _ x hx)⟩

end RAFReactionQuotient
