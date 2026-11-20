module

public import PottsDiscontinuity.RCInfinite.SpatialComparison

@[expose] public section

open MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.RCInfinite
open FK

private theorem limit_joint_compare (θ : Parameters) (i : Fin 2) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (m : ℕ) (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges (0, 0) m)
    (B : Set LatticeConfiguration) (hB : IsCylinder B)
    (hout : DependsOn (boxEdges (0, 0) m)ᶜ B) :
    comparisonSign i * μ.real (LatticeConfiguration.allOpen F ∩ B) ≤
      comparisonSign i * (boxMeasure θ i (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) * μ.real B := by
  apply le_of_tendsto_of_tendsto
    ((tendsto_cylinder_probability θ i μ hμ ((isCylinder_allOpen F).inter hB)).const_mul _)
    ((tendsto_cylinder_probability θ i μ hμ hB).const_mul _)
  filter_upwards [eventually_ge_atTop m] with n hn
  exact box_joint_compare θ i (latticeBox_mono (0, 0) hn) F hF B hB.measurableSet hout

private theorem abs_covariance_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (A B : Set X) (hB : MeasurableSet B)
    (s u : ℝ) (hs : |s| = 1)
    (h : s * μ.real (A ∩ B) ≤ s * u * μ.real B)
    (hc : s * μ.real (A ∩ Bᶜ) ≤ s * u * μ.real Bᶜ) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ |u - μ.real A| := by
  have hbc : μ.real Bᶜ = 1 - μ.real B := by
    simp [measureReal_compl hB]
  have hjc : μ.real (A ∩ Bᶜ) = μ.real A - μ.real (A ∩ B) := by
    have hsum := measureReal_inter_add_sdiff (μ := μ) (s := A) (t := B) hB
    change μ.real (A ∩ B) + μ.real (A ∩ Bᶜ) = μ.real A at hsum
    linarith only [hsum]
  rw [hbc, hjc] at hc
  have hd : 0 ≤ s * (u - μ.real A) := by linarith only [h, hc]
  have hx : |s * (μ.real (A ∩ B) - μ.real A * μ.real B)| ≤ s * (u - μ.real A) := by
    rw [abs_le]
    constructor
    · nlinarith only [hc, mul_nonneg hd (measureReal_nonneg (μ := μ) (s := B))]
    · nlinarith only [h, mul_nonneg hd (sub_nonneg.mpr (measureReal_le_one (μ := μ) (s := B)))]
  simpa [hs] using hx.trans (le_abs_self _)

/-- Uniform decorrelation from the exterior of a box. The right side is the
single-cylinder box-limit error and is independent of the exterior event. -/
theorem cylinder_exterior_covariance_bound (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (m : ℕ) (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges (0, 0) m)
    (B : Set LatticeConfiguration) (hB : IsCylinder B)
    (hout : DependsOn (boxEdges (0, 0) m)ᶜ B) :
    |μ.real (LatticeConfiguration.allOpen F ∩ B) -
      μ.real (LatticeConfiguration.allOpen F) * μ.real B| ≤
      |(boxMeasure θ i (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) - μ.real (LatticeConfiguration.allOpen F)| := by
  have : IsProbabilityMeasure μ := hμ.1
  exact abs_covariance_le μ _ B hB.measurableSet _ _ (abs_comparisonSign i)
    (limit_joint_compare θ i μ hμ m F hF B hB hout)
    (limit_joint_compare θ i μ hμ m F hF Bᶜ hB.compl hout.compl)

end PottsDiscontinuity.RCInfinite
