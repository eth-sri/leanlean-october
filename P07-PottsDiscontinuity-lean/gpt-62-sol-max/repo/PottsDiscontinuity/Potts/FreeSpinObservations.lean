module

public import PottsDiscontinuity.Potts.FreeCylinderPartition
public import PottsDiscontinuity.Potts.SpinObservation

/-! General finite observations of any free Potts box limit. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
section

variable {A : Type*} [Fintype A]
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (v : A → ℤ × ℤ) (ξ : A → Set.Icc 1 q)

include hφ in
theorem free_spin_observation_tendsto :
    Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ 0 n).toMeasure.real
      (spinObservationEvent q v ξ)) atTop
      (𝓝 (partitionExpectation φ.toMeasure (infiniteFreePartition v) (fun R => clusterCylinderProbability R id ξ))) :=
  tendsto_pottsBox_observed q hq β hβ 0 v ξ
    (free_partitionExpectation_tendsto (fkParameters q hq β hβ) φ hφ v _)
    (fun n _ hv => potts_free_cylinder_eq_partitionExpectation q hq β hβ n v hv ξ)

end

/-- The colouring formula holds for any finite family of observations, including
repeated vertices, under any frozen free Potts box limit. -/
theorem free_spin_observation_formula {A : Type*} [Fintype A]
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q)) (hμ : IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure)
    (v : A → ℤ × ℤ) (ξ : A → Set.Icc 1 q) :
    μ.toMeasure.real (spinObservationEvent q v ξ) =
      partitionExpectation φ.toMeasure (infiniteFreePartition v) (fun R => clusterCylinderProbability R id ξ) := by
  exact tendsto_nhds_unique (ProbabilityMeasure.tendsto_real_clopen
    (box_tendsto_of_isPottsInfiniteVolumeLimit q hq β hβ 0 μ hμ) (spinObservationEvent_isClopen q v ξ))
    (free_spin_observation_tendsto q hq β hβ φ hφ v ξ)

end
end PottsDiscontinuity.Potts
