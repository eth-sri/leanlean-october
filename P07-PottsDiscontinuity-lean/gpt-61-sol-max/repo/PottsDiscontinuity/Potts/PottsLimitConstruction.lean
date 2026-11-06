module
public import Mathlib

public import PottsDiscontinuity.Potts.PottsBoxLaws

/-! Assemble actual frozen Potts limits from proved real cylinder limits. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory Filter Topology
noncomputable section

theorem potts_limit_of_cylinder_limits (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (L : Finset (ℤ × ℤ) → SpinSpace q → ℝ)
    (hL : ∀ A ξ, Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real
      (spinCylinder q A ξ)) atTop (𝓝 (L A ξ))) :
    ∃ μ : ProbabilityMeasure (SpinSpace q), IsPottsInfiniteVolumeLimit q β i μ.toMeasure ∧
      ∀ A ξ, μ.toMeasure.real (spinCylinder q A ξ) = L A ξ := by
  have hnonneg (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q)  :=
    ge_of_tendsto (hL A ξ) (Filter.Eventually.of_forall  fun _ => measureReal_nonneg )
  
  
  obtain ⟨μ, ⟨hweak, hcoords⟩, _⟩ :=
    probabilityMeasures_tendsto_of_spinCylinder_tendsto q hq (pottsBoxProbabilityMeasure q hq β hβ i) (fun z => ⟨L z.1 z.2, hnonneg z.1 z.2⟩)  fun A ξ => by
                                                                                                             apply NNReal.tendsto_coe.mp
                                                                                                             change Tendsto (fun n => ( pottsBoxProbabilityMeasure q hq β hβ i n (spinCylinder q A ξ)  : ℝ))
                                                                                                               atTop (𝓝 (L A ξ))
                                                                                                             simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using hL A ξ 
  refine ⟨μ, isPottsInfiniteVolumeLimit_of_box_tendsto q hq β hβ i μ hweak, ?_⟩
  intro A ξ
  have h := congrArg (fun x : NNReal => (x : ℝ)) (hcoords A ξ)
  change (μ (spinCylinder q A ξ) ) = L A ξ at h
  simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn] using h

end
end PottsDiscontinuity.Potts
