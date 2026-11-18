module

public import proofs.HordijkSteelThreshold.FixedBaseSprinkling

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal

theorem measurableSet_reversibleUnbounded (L : ℕ) :
    MeasurableSet {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} := by
  have he : {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} =
      ⋂ K : ℕ, ⋃ w : List Bool, ⋃ (_h : K < w.length),
        {field | InfiniteReversibleGenerated L field w} := by
    ext field
    simp [ReversibleUnbounded]
  rw [he]
  exact MeasurableSet.iInter (fun _ => MeasurableSet.iUnion (fun w =>
    MeasurableSet.iUnion (fun _ => measurableSet_infiniteReversibleGenerated L w)))

end HordijkSteelThreshold
