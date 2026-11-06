module

public import proofs.HordijkSteelThreshold.ReversibleEscape
public import proofs.HordijkSteelThreshold.InfiniteStaticLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval

def staticEscapeEvent (L K : ℕ) : Set (Reaction (2*(K+L)) → Prop) :=
  {ω | ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω),
    K+L < (moleculeWord x).length}

theorem finite_static_escape_measure_eq (L K : ℕ) (a : I) :
    staticReactionMeasure (2*(K+L)) a (staticEscapeEvent L K) =
      infiniteStaticMeasure a (reversibleEscapeEvent L K) := by
  rw [← infiniteStatic_restriction_map (2*(K+L)) a,
    Measure.map_apply (measurable_splitRestriction _) (Set.toFinite _).measurableSet]
  congr 1; ext field
  simp only [Set.mem_preimage, staticEscapeEvent, reversibleEscapeEvent, Set.mem_ofPred_eq]
  exact ⟨fun ⟨x, hx, hl⟩ => ⟨_, hl, literalClosure_to_finiteReversible field x hx⟩,
    fun ⟨w, hw, hg⟩ => let ⟨x, hx, he⟩ := finiteReversible_to_literalClosure hg; ⟨x, hx, he.symm ▸ hw⟩⟩

theorem reversible_escape_probability_tendsto (μ : Measure InfiniteSplitEnvironment)
    [IsProbabilityMeasure μ] (L : ℕ) :
    Filter.Tendsto (fun K => μ (reversibleEscapeEvent L K))
      Filter.atTop (nhds (μ {field | ReversibleUnbounded L field})) := by
  rw [← reversibleEscapeEvent_inter L]
  exact tendsto_measure_iInter_atTop
    (fun K => (measurableSet_reversibleEscapeEvent L K).nullMeasurableSet)
    (reversibleEscapeEvent_antitone L) ⟨0, measure_ne_top μ _⟩

theorem finite_static_escape_probability_tendsto (a : I) :
    Filter.Tendsto (fun K => staticReactionMeasure (2*(K+2)) a (staticEscapeEvent 2 K))
      Filter.atTop (nhds (infiniteStaticMeasure a {field | ReversibleUnbounded 2 field})) := by
  simp_rw [finite_static_escape_measure_eq]
  exact reversible_escape_probability_tendsto (infiniteStaticMeasure a) 2

end HordijkSteelThreshold
