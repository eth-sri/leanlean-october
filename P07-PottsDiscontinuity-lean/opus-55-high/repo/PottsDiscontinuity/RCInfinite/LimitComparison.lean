module

public import PottsDiscontinuity.RCInfinite.SpatialComparison

public section

open MeasureTheory Filter Topology Set

namespace PottsDiscontinuity.RCInfinite
open FK

section
variable (θ : Parameters) (μ : Measure LatticeConfiguration)
theorem wired_limit_joint_le (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ)
    (m : ℕ) (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges (0, 0) m)
    (B : Set LatticeConfiguration) (hB : IsCylinder B)
    (hout : DependsOn (boxEdges (0, 0) m)ᶜ B) :
    μ.real (LatticeConfiguration.allOpen F ∩ B) ≤
      (wiredBoxProbabilityMeasure θ (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) * μ.real B := by
  apply le_of_tendsto_of_tendsto
    (tendsto_cylinder_probability θ 1 μ hμ ((isCylinder_allOpen F).inter hB))
    (tendsto_const_nhds.mul (tendsto_cylinder_probability θ 1 μ hμ hB))
  filter_upwards [eventually_ge_atTop m] with n hn
  simpa only [boxMeasure_wired] using
    wired_box_joint_le θ (latticeBox_mono (0, 0) hn) F hF B hB.measurableSet hout

theorem free_limit_joint_ge (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (m : ℕ) (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges (0, 0) m)
    (B : Set LatticeConfiguration) (hB : IsCylinder B)
    (hout : DependsOn (boxEdges (0, 0) m)ᶜ B) :
    (boxProbabilityMeasure θ (0, 0) m : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) * μ.real B ≤
      μ.real (LatticeConfiguration.allOpen F ∩ B) := by
  apply le_of_tendsto_of_tendsto
    (tendsto_const_nhds.mul (tendsto_cylinder_probability θ 0 μ hμ hB))
    (tendsto_cylinder_probability θ 0 μ hμ ((isCylinder_allOpen F).inter hB))
  filter_upwards [eventually_ge_atTop m] with n hn
  simpa only [boxMeasure_free] using
    free_box_joint_ge θ (latticeBox_mono (0, 0) hn) F hF B hB.measurableSet hout
end

section Arithmetic
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

section
variable (A B : Set X) (hB : MeasurableSet B)
include hB
theorem abs_covariance_le_of_upper (u : ℝ)
    (h : μ.real (A ∩ B) ≤ u * μ.real B)
    (hc : μ.real (A ∩ Bᶜ) ≤ u * μ.real Bᶜ) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ u - μ.real A := by
  have hsumB : μ.real B + μ.real Bᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) hB
  have hsumA : μ.real (A ∩ B) + μ.real (A ∩ Bᶜ) = μ.real A := by
    have ht := measureReal_inter_add_sdiff (μ := μ) hB
    tauto
  have hbc : μ.real Bᶜ = 1 - μ.real B := by linarith
  simp_all
  have hδ : 0 ≤ u - μ.real A := by linarith
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hδ (measureReal_nonneg (μ := μ) (s := B))]
  · nlinarith [mul_nonneg hδ (sub_nonneg.mpr (measureReal_le_one (μ := μ) (s := B)))]

theorem abs_covariance_le_of_lower (l : ℝ)
    (h : l * μ.real B ≤ μ.real (A ∩ B))
    (hc : l * μ.real Bᶜ ≤ μ.real (A ∩ Bᶜ)) :
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤ μ.real A - l := by
  have hsumB : μ.real B + μ.real Bᶜ = 1 := by
    simpa using measureReal_add_measureReal_compl (μ := μ) hB
  have hsumA : μ.real (A ∩ B) + μ.real (A ∩ Bᶜ) = μ.real A := by
    have ht := measureReal_inter_add_sdiff (μ := μ) hB
    tauto
  have hbc : μ.real Bᶜ = 1 - μ.real B := by linarith
  simp_all
  have hδ : 0 ≤ μ.real A - l := by linarith
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hδ (sub_nonneg.mpr (measureReal_le_one (μ := μ) (s := B)))]
  · nlinarith [mul_nonneg hδ (measureReal_nonneg (μ := μ) (s := B))]
end

end Arithmetic

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
  have  := hμ.1
  fin_cases i
  · have h := abs_covariance_le_of_lower μ _ B hB.measurableSet _
      (free_limit_joint_ge θ μ hμ m F hF B hB hout)
      (free_limit_joint_ge θ μ hμ m F hF Bᶜ hB.compl hout.compl)
    grind [boxMeasure]
  · simpa [boxMeasure] using (abs_covariance_le_of_upper μ _ B hB.measurableSet _
      (wired_limit_joint_le θ μ hμ m F hF B hB hout)
      (wired_limit_joint_le θ μ hμ m F hF Bᶜ hB.compl hout.compl)).trans
        (le_abs_self _)

end PottsDiscontinuity.RCInfinite
