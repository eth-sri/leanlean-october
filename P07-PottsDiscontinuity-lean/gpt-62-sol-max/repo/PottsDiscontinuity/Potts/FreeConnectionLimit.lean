module

public import PottsDiscontinuity.Infra.ClopenProbability

public import PottsDiscontinuity.Potts.FreeBoxObservation
public import PottsDiscontinuity.Potts.FreeConnectionEvents
public import PottsDiscontinuity.Potts.MonotoneEventLimits

/-! Free connection-data limits use actual connections, without merging. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

/-- Every finite collection of free connections converges to the actual
open-graph connections under the free box limit. -/
theorem free_connection_moments_tendsto (θ : FK.Parameters)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.boxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (F : Finset ((ℤ × ℤ) × (ℤ × ℤ))) :
    Tendsto (fun n => (closedBoxProbabilityMeasure θ n).toMeasure.real (freeDataEvent n F))
      atTop (𝓝 (μ.toMeasure.real (infiniteFreeDataEvent F))) := by
  rw [← iUnion_freeDataEvent F]
  apply increasing_event_diagonal_tendsto _ μ _ (freeDataEvent_monotone F)
  · intro m
    simpa only [closedBoxProbabilityMeasure_eq_free] using
      ProbabilityMeasure.tendsto_real_clopen hμ (freeDataEvent_isClopen m F)
  · intro n
    simpa only [RCInfinite.comparisonSign_zero, neg_one_mul, neg_le_neg_iff, RCInfinite.boxMeasure_free,
      ← closedBoxProbabilityMeasure_eq_free, ← freeDataEvent_eq_observation] using
      boxObservation_limit_compare θ 0 μ hμ n (freeDataFiniteEvent n F) (freeDataFiniteEvent_upper n F)

end
end PottsDiscontinuity.Potts
