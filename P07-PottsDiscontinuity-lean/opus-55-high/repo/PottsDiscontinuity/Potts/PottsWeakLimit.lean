module

public import PottsDiscontinuity.Potts.PottsBoxLaws

/-! The frozen cylinder-limit predicate determines weak convergence of the box laws. -/

public section

namespace PottsDiscontinuity.Potts

open MeasureTheory Filter Topology
noncomputable section

theorem box_tendsto_of_isPottsInfiniteVolumeLimit (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (μ : ProbabilityMeasure (SpinSpace q))
    (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure) :
    Tendsto (pottsBoxProbabilityMeasure q hq β hβ i) atTop (𝓝 μ) := by
  have hemb := (continuous_spinCylinderCoordinates q).isClosedEmbedding
    (spinCylinderCoordinates_injective q hq)
  apply hemb.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  rintro ⟨A, ξ⟩
  apply NNReal.tendsto_coe.mp
  have ht := hμ.2 A ξ
  have he : ∀ᶠ n : ℕ in atTop,
      (∑ σ : SpinConfiguration q (box n),
        if ∀ x ∈ A, ∃ h : x ∈ box n, σ ⟨x, h⟩ = ξ x then pottsProb q (box n) β i σ else 0) =
        (pottsBoxProbabilityMeasure q hq β hβ i n).toMeasure.real (spinCylinder q A ξ) := by
    filter_upwards [((eventually_all_finset A).mpr (fun x _ => FK.eventually_mem_box x))] with n hn
    exact (pottsBoxProbabilityMeasure_cylinder q hq β hβ i n A ξ hn).symm
  have hreal := ht.congr' he
  tauto

end
end PottsDiscontinuity.Potts
