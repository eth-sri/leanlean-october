/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.NormalizerEndpoint
public import BergmanWeakType.Weighted.MassCoordinate
public import BergmanWeakType.WeakType

/-! # Admissible annular inputs for positive weighted sharpness -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped Topology

namespace BergmanWeakType
open Weighted

private def outerAnnulus (α t : ℝ) : Set ℂ := {w | massRadius α t < ‖w‖}

private theorem restrict_annulus {α t : ℝ} (hα : -1 < α) (ht : t ∈ openRadii) :
    (weightedArea α).restrict (outerAnnulus α t) =
      ((volume.restrict (Ioo 0 t)).prod angleMeasure).map (massMap α) := by
  have hmeas : MeasurableSet (outerAnnulus α t) := measurableSet_lt measurable_const measurable_norm
  rw [weightedArea_eq_map_mass hα, Measure.restrict_map (measurable_massMap α) hmeas]
  rw [Measure.restrict_prod_eq_prod_univ (openRadii),
    Measure.restrict_restrict (hmeas.preimage (measurable_massMap α)),
    Measure.restrict_prod_eq_prod_univ (Ioo 0 t)]
  congr 2
  ext ⟨y, θ⟩
  simp only [mem_inter_iff, mem_prod, mem_univ, and_true]
  by_cases hy : y ∈ openRadii
  · simp [hy, outerAnnulus, abs_of_pos (massRadius_mem_unit hα hy).1,
      (massRadius_strictAntiOn hα).lt_iff_gt ht hy, hy.1]
  · have hn : y ∉ Ioo 0 t := fun h ↦ hy (Ioo_subset_Ioo_right ht.2.le h)
    simp [hy, hn]

private theorem area_annulus {α t : ℝ} (hα : -1 < α) (ht : t ∈ openRadii) :
    weightedArea α (outerAnnulus α t) = ENNReal.ofReal t := by
  rw [← Measure.restrict_apply_univ, restrict_annulus hα ht, Measure.map_apply
    (measurable_massMap α) MeasurableSet.univ, preimage_univ, ← univ_prod_univ, Measure.prod_prod]
  simp

/-- Admissible outer-annulus inputs recover the exact positive weighted lower constant. -/
theorem gammaConstant_le_weightedPositiveProjection_constant (α : ℝ) (hα : -1 < α) :
    ENNReal.ofReal (gammaConstant α) ≤
      weakTypeConstant (weightedArea α) (weightedPositiveProjection α) := by
  let := weightedArea_isProbabilityMeasure α hα
  apply le_sInf
  intro C hC
  apply le_of_tendsto (ENNReal.tendsto_ofReal (tendsto_radialMass_mul_normalizer hα))
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with R hR
  have hR' := radiusMass_mem_unit hα hR
  have hc := (continuousOn_normalizer α).continuousAt (Ico_mem_nhds hR.1 hR.2)
  have hlim : Filter.Tendsto (fun r : ℝ ↦ normalizer α (r * R)) (𝓝[<] 1) (𝓝 (normalizer α R)) :=
    hc.tendsto.comp <| by
      simpa using (continuousAt_id.mul_const R).tendsto.mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
  apply le_of_tendsto (ENNReal.tendsto_ofReal (hlim.const_mul (radiusMass α R)))
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  let t := radiusMass α r
  let A := outerAnnulus α t
  have ht := radiusMass_mem_unit hα hr
  have hn := normalizer_nonneg α (r * R)
  change ENNReal.ofReal (radiusMass α R * normalizer α (r * R)) ≤ C
  rw [mul_comm, ENNReal.ofReal_mul hn, ← area_annulus hα hR']
  have hA : MeasurableSet A := measurableSet_lt measurable_const measurable_norm
  refine hC.test_indicator hA (by rw [area_annulus hα ht]; simp_all) hn ?_
  filter_upwards [ae_mem_disk_weightedArea α] with z hzd hz
  let K := fun w ↦ ENNReal.ofReal ‖weightedKernel α z w‖
  have hK : Measurable K := by simp_rw [K, norm_weightedKernel]; fun_prop
  have he : (fun w ↦ K w * ‖A.indicator (fun _ ↦ (1 : ℂ)) w‖ₑ) = A.indicator K := by
    ext w; by_cases hw : w ∈ A <;> simp [hw]
  rw [weightedPositiveProjection, he, lintegral_indicator hA,
    restrict_annulus hα ht, lintegral_map hK (measurable_massMap α),
    lintegral_prod (fun p ↦ K (massMap α p)) (hK.comp (measurable_massMap α)).aemeasurable,
    ENNReal.ofReal_mul hn, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    area_annulus hα ht]
  trans ∫⁻ _ in Ioo 0 t, ENNReal.ofReal (normalizer α (r * R))
  · simp [t]
  apply setLIntegral_mono' measurableSet_Ioo
  intro y hy
  have hy' : y ∈ openRadii := ⟨hy.1, hy.2.trans ht.2⟩
  have hr' := massRadius_mem_unit hα hy'
  have hθ : Measurable (fun θ ↦ ‖weightedKernel α z (massMap α (y, θ))‖) := by
    simp only [norm_weightedKernel, massMap]
    fun_prop
  refine le_trans ?_ ENNReal.ofReal_toReal_le
  rw [← integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ ↦ norm_nonneg _) hθ.aestronglyMeasurable]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [massMap]
  rw [← circleAverage_eq_integral_angleMeasure (fun w ↦ ‖weightedKernel α z w‖) 0 _, circleAverage_weightedKernel_norm]
  have hz1 := (mem_disk_iff z).mp hzd
  have hz2 : R ≤ ‖z‖ := (mass_massRadius hα hR) ▸ hz.le
  have hrr : r ≤ massRadius α y := by
    rw [← mass_massRadius hα hr]
    exact (massRadius_strictAntiOn hα).antitoneOn hy' ht hy.2.le
  exact normalizer_mono α (by positivity [hr.1, hR.1]) (by gcongr <;> positivity [hr'.1, hR.1]) (by nlinarith [norm_nonneg z, hr'.2])

end BergmanWeakType
