module

public import proofs.RAFCriticalWindowQuantitative.ExplicitTruncation
public import proofs.RAFCriticalWindowQuantitative.QuotientExplicitTruncation
public import proofs.HordijkSteelThreshold.StaticSurvivalContinuity

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal

theorem split_escape_finite (a : I) (K : ℕ) (hK : 2 ≤ K) :
    splitEscapeProbability a K =
      staticReactionMeasure (2*((K-2)+2)) a (staticEscapeEvent 2 (K-2)) := by
  rw [splitEscapeProbability, finite_static_escape_measure_eq, infiniteStaticMeasure,
    Measure.map_apply measurable_currySplitField (measurableSet_reversibleEscapeEvent 2 (K-2))]
  congr 1; ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, reversibleEscapeEvent_iff, Nat.sub_add_cancel hK]

theorem split_survival_le_escape (a : I) (K : ℕ) : staticSurvival a ≤ splitEscapeProbability a K := by
  rw [staticSurvival, infiniteStaticMeasure,
    Measure.map_apply measurable_currySplitField (measurableSet_reversibleUnbounded 2)]
  exact measure_mono fun ω hω => hω K

theorem quotient_escape_finite (a : I) (K : ℕ) (hK : 2 ≤ K) :
    quotientEscapeProbability a K =
      quotientStaticMeasure (2*((K-2)+2)) a (quotientEscapeEvent 2 (K-2)) := by
  rw [quotientEscapeProbability, quotient_escape_measure_eq, quotientInfiniteMeasure,
    Measure.map_apply quotientField_measurable (measurableSet_reversibleEscapeEvent 2 (K-2))]
  congr 1; ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, reversibleEscapeEvent_iff, Nat.sub_add_cancel hK]

theorem quotient_survival_le_escape (a : I) (K : ℕ) :
    quotientSurvival a ≤ quotientEscapeProbability a K :=
  measure_mono fun _ hω => hω K

end RAFCriticalWindowQuantitative
