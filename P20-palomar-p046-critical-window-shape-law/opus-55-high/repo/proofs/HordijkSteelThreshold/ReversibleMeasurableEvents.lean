module

public import proofs.HordijkSteelThreshold.ReversibleClosureDock

public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete

variable (N L : ℕ)

variable (w : List Bool)

theorem measurable_finiteReversibleGenerated   :
    Measurable (fun field : InfiniteSplitEnvironment => FiniteReversibleGenerated N L field w) := by
  simp_rw [finiteReversible_iff_literalClosure, restrictedSplitReactions]
  exact (measurable_of_finite fun ω : Reaction N → Prop => ∃ x ∈ temporaryReactionClosure L
    (Finset.univ.filter ω), moleculeWord x = w).comp $ by fun_prop

theorem measurableSet_finiteReversibleGenerated   :
    MeasurableSet {field : InfiniteSplitEnvironment | FiniteReversibleGenerated N L field w} :=
  measurableSet_setOfPred.2 $ measurable_finiteReversibleGenerated N L w


theorem measurableSet_infiniteReversibleGenerated (L : ℕ) (w : List Bool) :
    MeasurableSet {field : InfiniteSplitEnvironment | InfiniteReversibleGenerated L field w} := by
  simp only [infiniteReversibleGenerated_iff_finite_certificate, Set.ofPred_exists]
  exact .iUnion fun N => measurableSet_finiteReversibleGenerated N L w

theorem measurableSet_finite_seed  (seed : Finset $ List Bool) :
    MeasurableSet {field : InfiniteSplitEnvironment |
      ∀ w ∈ seed, FiniteReversibleGenerated N L field w} := by
  simp only [Set.ofPred_forall]
  exact Finset.measurableSet_biInter seed fun w _ => measurableSet_finiteReversibleGenerated N L w


/-- Finite seed probabilities approximate the infinite seed event under any
fixed measure on the countable split environment. No cap exchange is assumed. -/
theorem finite_seed_probability_tendsto (μ : Measure InfiniteSplitEnvironment)
    (L : ℕ) (seed : Finset $ List Bool) :
    Filter.Tendsto (fun N => μ {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w})
      Filter.atTop (nhds $ μ {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w}) := by
  convert tendsto_measure_iUnion_atTop (μ := μ)
    (s := fun N => {field | ∀ w ∈ seed, FiniteReversibleGenerated N L field w}) fun N M h field hf w hw =>
    finiteReversibleGenerated_mono_cap h (hf w hw) using 3
  · rfl
  ext field
  simp_all
  refine ⟨fun h => ?_, fun ⟨N, hN⟩ w hw => finiteReversibleGenerated_to_infinite $ hN w hw⟩
  choose! f hf using fun w hw => infiniteReversibleGenerated_finite_certificate $ h w hw
  exact ⟨seed.sup f, fun w hw => finiteReversibleGenerated_mono_cap (Finset.le_sup hw) $ hf w hw⟩

end HordijkSteelThreshold
