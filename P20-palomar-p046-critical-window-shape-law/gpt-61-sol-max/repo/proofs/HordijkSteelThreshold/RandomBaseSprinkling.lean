
import proofs.HordijkSteelThreshold.UnboundedTrialExtraction
import proofs.HordijkSteelThreshold.InfiniteStaticLaw
import proofs.HordijkSteelThreshold.TargetTrials
import proofs.HordijkSteelThreshold.StaticSeedClosure
import proofs.HordijkSteelThreshold.WordEffectiveClosure



namespace HordijkSteelThreshold

theorem measurableSet_reversibleUnbounded (L : ℕ) :
    MeasurableSet {field : InfiniteSplitEnvironment | ReversibleUnbounded L field} := by
  apply Measurable.setOf
  unfold ReversibleUnbounded
  fun_prop

end HordijkSteelThreshold
