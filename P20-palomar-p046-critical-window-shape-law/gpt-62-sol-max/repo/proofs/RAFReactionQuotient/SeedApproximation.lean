module

public import proofs.RAFReactionQuotient.FiniteApproximation
public import proofs.HordijkSteelThreshold.SourceTerminalRAF

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
  apply (measure_mono (show {q : RepositoryChannel N → Prop | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ quotientClosure N 2 (quotientOpen q), moleculeWord x = w} ⊆
      {q | (m-1)*Fintype.card (Molecule N) ≤ m*(quotientClosure N 2 (quotientOpen q)).card} ∪
      {q | m*(quotientClosure N L (quotientOpen q)).card < (m-1)*Fintype.card (Molecule N)} from ?_)).trans
      (measure_union_le _ _)
  intro q hseed
  by_cases hb : m*(quotientClosure N L (quotientOpen q)).card < (m-1)*Fintype.card (Molecule N)
  · exact Or.inr hb
  · left
    have hs : quotientClosure N L (quotientOpen q) ⊆ quotientClosure N 2 (quotientOpen q) := by
      simp only [quotientClosure_pullback] at hseed ⊢
      apply temporaryReactionClosure_seed_transfer Finset.Subset.rfl
      intro x hx
      have hw : moleculeWord x ∈ actualBinaryWords L :=
        (mem_actualBinaryWords _ _).mpr ⟨moleculeWord_nonempty x,by rwa [moleculeWord_length]⟩
      obtain ⟨y,hy,he⟩ := hseed _ hw
      exact moleculeWord_injective he ▸ hy
    exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hs))

theorem quotient_capped_escape_le (N K : ℕ) (a : I) :
    quotientStaticMeasure N a {q | ∃ x ∈ quotientClosure N 2 (quotientOpen q), K+2 < molLength x} ≤
      quotientInfiniteMeasure a (reversibleEscapeEvent 2 K) := by
  rw [← infinite_quotient_restriction_map N a,
    Measure.map_apply (Measurable.of_eval (fun j => measurable_pi_apply _))
      (Set.toFinite _).measurableSet,
    quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
      (measurableSet_reversibleEscapeEvent 2 K)]
  apply measure_mono
  intro ω h
  change ∃ x ∈ quotientClosure N 2 (quotientOpen (fun j => ω (quotientCoordinate j))),
    K+2 < molLength x at h
  rw [quotientClosure_restriction] at h
  obtain ⟨x,hx,hl⟩ := h
  apply (reversibleEscapeEvent_iff 2 K (quotientField ω)).mpr
  exact ⟨moleculeWord x,by simpa only [moleculeWord_length] using hl,
    finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible _ x hx)⟩

end RAFReactionQuotient
