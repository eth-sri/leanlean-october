
import proofs.HordijkSteelThreshold.UnboundedTrialExtraction
import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound




namespace HordijkSteelThreshold

section
variable {L K : ℕ} (hLK : L ≤ K)

include hLK in
/-- If generation ever leaves length K, its first escape fits within cap 2K.
Cleavage cannot create the first longer word. -/
theorem reversible_generated_or_escape 
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L field w) :
    FiniteReversibleGenerated (2*K) L field w ∨
      ∃ v, K < v.length ∧ FiniteReversibleGenerated (2*K) L field v := by
  induction h <;> grind [FiniteReversibleGenerated]

include hLK in
theorem reversible_escape_iff_cap 
    (field : InfiniteSplitEnvironment) :
    (∃ w, K < w.length ∧ InfiniteReversibleGenerated L field w) ↔
      ∃ w, K < w.length ∧ FiniteReversibleGenerated (2*K) L field w := by grind [reversible_generated_or_escape, finiteReversibleGenerated_to_infinite]

variable (L K : ℕ)

def reversibleEscapeEvent   :=
  {field | ∃ w, K+L < w.length ∧ FiniteReversibleGenerated (2*(K+L)) L field w}

theorem reversibleEscapeEvent_iff  (field : InfiniteSplitEnvironment) :
    field ∈ reversibleEscapeEvent L K ↔
      ∃ w, K+L < w.length ∧ InfiniteReversibleGenerated L field w :=
  (reversible_escape_iff_cap (by omega) field).symm



theorem measurableSet_reversibleEscapeEvent  :
    MeasurableSet (reversibleEscapeEvent L K) := by
  apply Measurable.setOf
  fun_prop
end

open MeasureTheory RAF.Polymer unitInterval

theorem reversible_escape_probability_tendsto
    (μ : Measure InfiniteSplitEnvironment) [IsFiniteMeasure μ] (L : ℕ) :
    Filter.Tendsto (fun K => μ (reversibleEscapeEvent L K)) Filter.atTop
      (nhds (μ {field | ReversibleUnbounded L field})) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun K => (measurableSet_reversibleEscapeEvent L K).nullMeasurableSet)
    (((by
       intro K M hKM field h
       grind [reversibleEscapeEvent_iff]))) ⟨0, measure_ne_top _ _⟩
  convert ht using 2 <;> try rfl
  congr 1
  symm
  ext field
  simp
  constructor
  · intro h K
    obtain ⟨w, hw, hg⟩ := (reversibleEscapeEvent_iff L K field).mp (h K)
    exact ⟨w, by omega, hg⟩
  exact?

variable (L K : ℕ)

def staticEscapeEvent  : Set (Reaction (2*(K+L)) → Prop) :=
  {ω | ∃ x ∈ temporaryReactionClosure L (staticOpenReactions ω),
    K+L < (moleculeWord x).length}

variable (a : I)

theorem finite_static_escape_measure_eq   :
    staticReactionMeasure _ a (staticEscapeEvent L K) =
      infiniteStaticMeasure a (reversibleEscapeEvent L K) := by
  rw [← infiniteStatic_restriction_map (2*(K+L)) a, Measure.map_apply]
  · congr 1
    ext field
    
    simp +instances only [staticEscapeEvent, reversibleEscapeEvent, Set.mem_preimage,
      Set.mem_ofPred_eq, finiteReversible_iff_literalClosure]
    aesop
  · apply Measurable.of_eval
    intro r
    exact (measurable_pi_apply _).comp (measurable_pi_apply _)
  · exact Set.Finite.measurableSet (Set.toFinite _)


end HordijkSteelThreshold
