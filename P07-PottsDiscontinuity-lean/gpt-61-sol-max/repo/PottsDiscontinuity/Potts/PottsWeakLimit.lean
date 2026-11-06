module
public import Mathlib

public import PottsDiscontinuity.Potts.PottsBoxLaws

/-! The frozen cylinder-limit predicate determines weak convergence of the box laws. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory Filter Topology
noncomputable section

theorem box_tendsto_of_isPottsInfiniteVolumeLimit (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure) :
    Tendsto (pottsBoxProbabilityMeasure q hq β hβ i) atTop (𝓝 μ) := by
  
  apply ((continuous_spinCylinderCoordinates q).isClosedEmbedding
           (spinCylinderCoordinates_injective q hq)).tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  rintro ⟨A, ξ⟩
  apply NNReal.tendsto_coe.mp
  have ht := hμ.2 A ξ
  change Tendsto _ atTop (𝓝 (μ.toMeasure.real (spinCylinder q A ξ))) at ht
   
  
  have hreal := ht.congr' (by
                             filter_upwards [ (eventually_all_finset A).mpr  fun x _ => FK.eventually_mem_box x ] with n hn
                             exact (pottsBoxProbabilityMeasure_cylinder q hq β hβ i n A ξ hn).symm)
  simpa only [spinCylinderCoordinates, Function.comp_def, ProbabilityMeasure.measureReal_eq_coe_coeFn] using hreal

end
end PottsDiscontinuity.Potts
