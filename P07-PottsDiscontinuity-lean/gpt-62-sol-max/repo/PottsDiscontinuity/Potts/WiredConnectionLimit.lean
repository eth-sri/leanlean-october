module

public import PottsDiscontinuity.Infra.ClopenProbability

public import PottsDiscontinuity.Potts.WiredConnectionEvents
public import PottsDiscontinuity.Potts.MonotoneEventLimits

/-! Convergence of wired connection data with every infinite cluster merged. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

/-- Every finite collection of required wired connections converges to the
corresponding merged infinite-cluster event. No infinite-cluster uniqueness is used. -/
theorem wired_connection_moments_tendsto (θ : FK.Parameters)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure θ (0, 0) n) atTop (𝓝 μ))
    (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    Tendsto (fun n => (openBoxProbabilityMeasure θ n).toMeasure.real (wiredDataEvent n F))
      atTop (𝓝 (μ.toMeasure.real (infiniteMergedDataEvent F))) := by
  rw [← iInter_wiredDataEvent F]
  apply decreasing_event_diagonal_tendsto _ μ _ (wiredDataEvent_antitone F)
    (fun n => (wiredDataEvent_isClopen n F).isOpen.measurableSet)
  · intro m
    simpa only [openBoxProbabilityMeasure_eq_wired] using
      ProbabilityMeasure.tendsto_real_clopen hμ (wiredDataEvent_isClopen m F)
  · intro n
    simpa only [RCInfinite.comparisonSign_one, one_mul, RCInfinite.boxMeasure_wired,
      ← openBoxProbabilityMeasure_eq_wired, ← wiredDataEvent_eq_observation] using
      boxObservation_limit_compare θ 1 μ hμ n (wiredDataFiniteEvent n F) (wiredDataFiniteEvent_upper n F)

end
end PottsDiscontinuity.Potts
