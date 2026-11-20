module

public import PottsDiscontinuity.Potts.ConditionedConnectionLimit
public import PottsDiscontinuity.Potts.FinitePartitionLimits
public import PottsDiscontinuity.Potts.FreeConnectionLimit

/-! Distributions and expectations of finite observed connection partitions. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

variable {A : Type*} [Fintype A]

def observedFreePartition (v : A → ℤ × ℤ) (n : ℕ) (ω : FK.LatticeConfiguration) : Setoid A :=
  (localFreeGraph (rcInfiniteOpenGraph ω) n).reachableSetoid.comap v

def infiniteFreePartition (v : A → ℤ × ℤ) (ω : FK.LatticeConfiguration) : Setoid A :=
  (rcInfiniteOpenGraph ω).reachableSetoid.comap v

def observedWiredPartition (v : A → Option (ℤ × ℤ)) (n : ℕ) (ω : FK.LatticeConfiguration) : Setoid A :=
  (localWiredSetoid (rcInfiniteOpenGraph ω) (n + 1)).comap v

def infiniteWiredPartition (v : A → Option (ℤ × ℤ)) (ω : FK.LatticeConfiguration) : Setoid A :=
  (infiniteMergedSetoid (rcInfiniteOpenGraph ω)).comap v

theorem infiniteFreeDataEvent_measurableSet (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    MeasurableSet (infiniteFreeDataEvent F) := by
  rw [← iUnion_freeDataEvent]
  exact MeasurableSet.iUnion fun n => (freeDataEvent_isClopen n F).isOpen.measurableSet

theorem infiniteMergedDataEvent_measurableSet (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    MeasurableSet (infiniteMergedDataEvent F) := by
  rw [← iInter_wiredDataEvent]
  exact MeasurableSet.iInter fun n => (wiredDataEvent_isClopen n F).isOpen.measurableSet

theorem free_observed_partition_tendsto (θ : FK.Parameters)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (v : A → ℤ × ℤ) (R : Setoid A) :
    Tendsto (fun n => (closedBoxProbabilityMeasure θ n).toMeasure.real
      {ω | observedFreePartition v n ω = R}) atTop
      (𝓝 (μ.toMeasure.real {ω | infiniteFreePartition v ω = R})) := by
  exact partition_probability_tendsto_comap _ μ v
    (fun n ω => (localFreeGraph (rcInfiniteOpenGraph ω) n).reachableSetoid)
    (fun ω => (rcInfiniteOpenGraph ω).reachableSetoid)
    (fun n F => (freeDataEvent_isClopen n F).isOpen.measurableSet)
    infiniteFreeDataEvent_measurableSet (free_connection_moments_tendsto θ μ hμ) R

theorem wired_observed_partition_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 μ)) (v : A → Option (ℤ × ℤ)) (R : Setoid A) :
    Tendsto (fun n => (conditionedOuterBoxProbabilityMeasure (fkParameters q hq β hβ) n).toMeasure.real
      {ω | observedWiredPartition v n ω = R}) atTop
      (𝓝 (μ.toMeasure.real {ω | infiniteWiredPartition v ω = R})) := by
  exact partition_probability_tendsto_comap _ μ v
    (fun n ω => localWiredSetoid (rcInfiniteOpenGraph ω) (n + 1))
    (fun ω => infiniteMergedSetoid (rcInfiniteOpenGraph ω))
    (fun n F => (wiredDataEvent_isClopen (n + 1) F).isOpen.measurableSet)
    infiniteMergedDataEvent_measurableSet (conditioned_connection_moments_tendsto q hq β hβ μ hμ) R

/-- Every function of the free observed partition, including its colouring
kernel, has convergent expectation. -/
theorem free_partitionExpectation_tendsto (θ : FK.Parameters)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (v : A → ℤ × ℤ) (K : Setoid A → ℝ) :
    Tendsto (fun n => partitionExpectation (closedBoxProbabilityMeasure θ n).toMeasure
      (observedFreePartition v n) K) atTop
      (𝓝 (partitionExpectation μ.toMeasure (infiniteFreePartition v) K)) :=
  partitionExpectation_tendsto _ μ _ _ K (free_observed_partition_tendsto θ μ hμ v)

/-- Every function of the merged wired observed partition has convergent expectation. -/
theorem wired_partitionExpectation_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 μ)) (v : A → Option (ℤ × ℤ)) (K : Setoid A → ℝ) :
    Tendsto (fun n => partitionExpectation
      (conditionedOuterBoxProbabilityMeasure (fkParameters q hq β hβ) n).toMeasure
      (observedWiredPartition v n) K) atTop
      (𝓝 (partitionExpectation μ.toMeasure (infiniteWiredPartition v) K)) :=
  partitionExpectation_tendsto _ μ _ _ K (wired_observed_partition_tendsto q hq β hβ μ hμ v)

end
end PottsDiscontinuity.Potts
