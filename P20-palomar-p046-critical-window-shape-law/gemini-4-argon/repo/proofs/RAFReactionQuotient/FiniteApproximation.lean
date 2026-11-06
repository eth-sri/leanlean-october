module

public import proofs.RAFReactionQuotient.InfiniteDock
public import proofs.RAFReactionQuotient.Richness

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

noncomputable def quotientInfiniteMeasure (a : I) : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map quotientField

noncomputable instance quotientInfinite_probability (a : I) :
    IsProbabilityMeasure (quotientInfiniteMeasure a) := by
  unfold quotientInfiniteMeasure; infer_instance

theorem quotientSurvival_eq (a : I) : quotientSurvival a =
    quotientInfiniteMeasure a {field | ReversibleUnbounded 2 field} := by
  rw [quotientInfiniteMeasure, Measure.map_apply quotientField_measurable
    (measurableSet_reversibleUnbounded 2)]
  rfl

theorem quotientClosure_pullback {n L : ℕ} (q : RepositoryChannel n → Prop) :
    quotientClosure n L (quotientOpen q) =
      temporaryReactionClosure L (staticOpenReactions (fun r => q (splitToQuotient r))) := by
  rw [← quotientClosure_OR, show fieldOR splitToQuotient (fun r => q (splitToQuotient r)) = q from
    funext fun j => propext (quotient_mark_pullback_OR q j)]

theorem quotientClosure_restriction (n L : ℕ) (ω : SplitField) :
    quotientClosure n L (quotientOpen (fun j => ω (quotientCoordinate j))) =
      temporaryReactionClosure L (restrictedSplitReactions n (quotientField ω)) := by
  rw [quotientClosure_pullback]
  congr 1; ext r
  simp only [staticOpenReactions, restrictedSplitReactions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.of_eq (by simpa only [literalSplitCoordinate, quotientField] using congrArg ω (canonicalIndex_split r).symm)

theorem quotient_finite_seed_tendsto (L : ℕ) (a : I) (seed : Finset (List Bool)) :
    Filter.Tendsto (fun n => quotientStaticMeasure n a {q | ∀ w ∈ seed,
      ∃ x ∈ quotientClosure n L (quotientOpen q), moleculeWord x = w}) Filter.atTop
      (nhds (quotientInfiniteMeasure a {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w})) := by
  have he (n : ℕ) : quotientStaticMeasure n a {q | ∀ w ∈ seed,
      ∃ x ∈ quotientClosure n L (quotientOpen q), moleculeWord x = w} =
    quotientInfiniteMeasure a {field | ∀ w ∈ seed, FiniteReversibleGenerated n L field w} := by
    rw [← infinite_quotient_restriction_map n a,
      Measure.map_apply (Measurable.of_eval fun _ => measurable_pi_apply _) (Set.toFinite _).measurableSet,
      quotientInfiniteMeasure, Measure.map_apply quotientField_measurable (measurableSet_finite_seed n L seed)]
    congr 1; ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, quotientClosure_restriction, finiteReversible_iff_literalClosure]
  simp_rw [he]
  exact finite_seed_probability_tendsto (quotientInfiniteMeasure a) L seed

def quotientEscapeEvent (L K : ℕ) : Set (RepositoryChannel (2*(K+L)) → Prop) :=
  {q | ∃ x ∈ quotientClosure (2*(K+L)) L (quotientOpen q), K+L < (moleculeWord x).length}

theorem quotient_escape_measure_eq (L K : ℕ) (a : I) :
    quotientStaticMeasure (2*(K+L)) a (quotientEscapeEvent L K) =
      quotientInfiniteMeasure a (reversibleEscapeEvent L K) := by
  rw [← infinite_quotient_restriction_map (2*(K+L)) a,
    Measure.map_apply (Measurable.of_eval fun _ => measurable_pi_apply _) (Set.toFinite _).measurableSet,
    quotientInfiniteMeasure, Measure.map_apply quotientField_measurable (measurableSet_reversibleEscapeEvent L K)]
  congr 1; ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, quotientEscapeEvent, quotientClosure_restriction,
    reversibleEscapeEvent]
  exact ⟨fun ⟨x, hx, hl⟩ => ⟨_, hl, literalClosure_to_finiteReversible _ x hx⟩,
    fun ⟨w, hw, hg⟩ => let ⟨x, hx, he⟩ := finiteReversible_to_literalClosure hg; ⟨x, hx, he.symm ▸ hw⟩⟩

theorem quotient_escape_tendsto (a : I) :
    Filter.Tendsto (fun K => quotientStaticMeasure (2*(K+2)) a (quotientEscapeEvent 2 K))
      Filter.atTop (nhds (quotientSurvival a)) := by
  simp_rw [quotient_escape_measure_eq, quotientSurvival_eq]
  exact reversible_escape_probability_tendsto (quotientInfiniteMeasure a) 2

end RAFReactionQuotient
