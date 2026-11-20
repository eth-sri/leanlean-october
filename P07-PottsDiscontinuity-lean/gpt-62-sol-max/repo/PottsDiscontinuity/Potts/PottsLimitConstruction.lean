module

public import PottsDiscontinuity.Potts.PottsBoxLaws

/-! Assemble actual frozen Potts limits from proved real cylinder limits. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory Filter Topology
noncomputable section

theorem potts_limit_of_cylinder_limits (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (μ : ProbabilityMeasure (SpinSpace q))
    (hL : ∀ A ξ, Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real
      (spinCylinder q A ξ)) atTop (𝓝 (μ.toMeasure.real (spinCylinder q A ξ)))) :
    IsPottsInfiniteVolumeLimit q β i μ.toMeasure :=
  isPottsInfiniteVolumeLimit_of_box_tendsto q hq β hβ i μ
    (probabilityMeasures_tendsto_of_spinCylinder_tendsto q hq _ μ hL)

end
end PottsDiscontinuity.Potts
