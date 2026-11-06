module
public import Mathlib

public import PottsDiscontinuity.Potts.FreeCylinderPartition
public import PottsDiscontinuity.Potts.PottsWeakLimit
public import PottsDiscontinuity.Potts.SpinObservation

/-! General finite observations of any free Potts box limit. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section
local instance freeObservationVertexDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq ↥(V : Set (ℤ × ℤ)) := fun _ _ => Classical.propDecidable _
local instance freeObservationVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype ↥(V : Set (ℤ × ℤ)) := Fintype.ofFinite _



/-- The colouring formula holds for any finite family of observations, including
repeated vertices, under any frozen free Potts box limit. -/
theorem free_spin_observation_formula {A : Type*} [Fintype A]
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto  (FK.boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0))  atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q)) (hμ : IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure)
    (v : A → ℤ × ℤ) (ξ : A → Set.Icc 1 q) :
    μ.toMeasure.real (spinObservationEvent q v ξ) =
      partitionExpectation φ.toMeasure (infiniteFreePartition v)  fun R => clusterCylinderProbability R id ξ  := by
   
  
  have hw := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (box_tendsto_of_isPottsInfiniteVolumeLimit q hq β hβ 0 μ hμ) (spinObservationEvent_isClopen q v ξ)
  have hr : Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ 0 n).toMeasure.real
      (spinObservationEvent q v ξ)) atTop (𝓝 (μ.toMeasure.real (spinObservationEvent q v ξ))) := by
    simp_all
  exact tendsto_nhds_unique hr (by
                                  apply (free_partitionExpectation_tendsto (fkParameters q hq β hβ) φ hφ v
                                            fun R => clusterCylinderProbability R id ξ).congr'
                                  
                                  filter_upwards [ Filter.eventually_all.mpr  fun a => FK.eventually_mem_box (v a)  ] with n hn
                                  exact ((pottsBoxProbabilityMeasure_observed q hq β hβ 0 n v hn ξ).trans
                                    (potts_free_cylinder_eq_partitionExpectation q hq β hβ n v hn ξ)).symm)

end
end PottsDiscontinuity.Potts
