module

public import proofs.HordijkSteelThreshold.UnboundedTrialExtraction
public import proofs.HordijkSteelThreshold.InfiniteStaticLaw
public import proofs.HordijkSteelThreshold.TargetTrials
public import proofs.HordijkSteelThreshold.StaticSeedClosure
public import proofs.HordijkSteelThreshold.StaticClosureMass

public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal

theorem measurableSet_reversibleUnbounded (L : ℕ) :
    MeasurableSet {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} := by
  have he : {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} =
      ⋂ K : ℕ, ⋃ w : List Bool, ⋃ (_h : K < w.length),
        {field | InfiniteReversibleGenerated L field w} := by
    aesop
  rw [he]
  exact MeasurableSet.iInter $ fun _ => MeasurableSet.iUnion $ fun w =>
    MeasurableSet.iUnion $ fun _ => measurableSet_infiniteReversibleGenerated L w

end HordijkSteelThreshold
