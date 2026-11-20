module

public import PottsDiscontinuity.Potts.ObservedPartitionLimits

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section

variable {A : Type*} [Fintype A]

theorem infiniteFreePartition_measurableSet (v : A → ℤ × ℤ) (R : Setoid A) :
    MeasurableSet {ω | infiniteFreePartition v ω = R} := by
  exact partition_event_measurable _ (measurable_comap_relation v (fun ω => (rcInfiniteOpenGraph ω).reachableSetoid)
    infiniteFreeDataEvent_measurableSet) R

theorem infiniteWiredPartition_measurableSet (v : A → Option (ℤ × ℤ)) (R : Setoid A) :
    MeasurableSet {ω | infiniteWiredPartition v ω = R} := by
  exact partition_event_measurable _ (measurable_comap_relation v (fun ω => infiniteMergedSetoid (rcInfiniteOpenGraph ω))
    infiniteMergedDataEvent_measurableSet) R

end
end PottsDiscontinuity.Potts
