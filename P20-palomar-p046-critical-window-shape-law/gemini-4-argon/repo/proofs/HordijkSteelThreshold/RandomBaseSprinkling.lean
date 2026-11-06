module

public import proofs.HordijkSteelThreshold.FixedBaseSprinkling

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory

theorem measurableSet_reversibleUnbounded (L : ℕ) :
    MeasurableSet {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} := by
  rw [show {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} =
    ⋂ K : ℕ, ⋃ w : List Bool, ⋃ (_ : K < w.length), {field | InfiniteReversibleGenerated L field w} by
      ext; simp [ReversibleUnbounded]]
  exact MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun w =>
    MeasurableSet.iUnion fun _ => measurableSet_infiniteReversibleGenerated L w

end HordijkSteelThreshold
