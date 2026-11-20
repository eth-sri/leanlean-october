/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Measure
public import BergmanWeakType.Kernel
public import BergmanWeakType.Weighted.AngleMeasure
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Order.IntermediateValue

/-! Polar integration in the uniform radial mass coordinate of weighted disk area. -/

@[expose] public section

noncomputable section
open MeasureTheory Set Real

namespace BergmanWeakType

abbrev radiusMass (α r : ℝ) : ℝ := (1 - r ^ 2) ^ (α + 1)
def massRadius (α y : ℝ) : ℝ := sqrt (1 - y ^ (α + 1)⁻¹)

lemma massRadius_mem_unit {α y : ℝ} (hα : -1 < α) (hy : y ∈ openRadii) :
    massRadius α y ∈ openRadii := by
  have hp : 0 < (α + 1)⁻¹ := inv_pos.mpr (by linarith)
  exact ⟨sqrt_pos.mpr (sub_pos.mpr (rpow_lt_one hy.1.le hy.2 hp)),
    (sqrt_lt' zero_lt_one).mpr (by simpa using sub_lt_self 1 (rpow_pos_of_pos hy.1 (α + 1)⁻¹))⟩

theorem massRadius_mass {α y : ℝ} (hα : -1 < α) (hy : y ∈ openRadii) :
    radiusMass α (massRadius α y) = y := by
  have hp : 0 < α + 1 := by linarith
  rw [radiusMass, massRadius, sq_sqrt (sub_nonneg.mpr (rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hp)).le),
    sub_sub_cancel, rpow_inv_rpow hy.1.le hp.ne']

theorem mass_massRadius {α r : ℝ} (hα : -1 < α) (hr : r ∈ openRadii) :
    massRadius α (radiusMass α r) = r := by
  have hp : 0 < α + 1 := by linarith
  rw [massRadius, radiusMass, rpow_rpow_inv (radial_defect_pos (Ioo_subset_Ico_self hr)).le hp.ne',
    sub_sub_cancel, sqrt_sq hr.1.le]

theorem massRadius_strictAntiOn {α : ℝ} (hα : -1 < α) : StrictAntiOn (massRadius α) openRadii := by
  intro y hy u hu hyu
  have hp : 0 < (α + 1)⁻¹ := inv_pos.mpr (by linarith)
  exact sqrt_lt_sqrt (sub_nonneg.mpr (rpow_le_one hu.1.le hu.2.le hp.le))
    (sub_lt_sub_left (rpow_lt_rpow hy.1.le hyu hp) 1)

theorem radiusMass_mem_unit {α r : ℝ} (hα : -1 < α) (hr : r ∈ openRadii) :
    radiusMass α r ∈ openRadii :=
  have hp := radial_defect_pos (Ioo_subset_Ico_self hr)
  ⟨rpow_pos_of_pos hp _, rpow_lt_one hp.le (sub_lt_self 1 (sq_pos_of_pos hr.1)) (by linarith)⟩

abbrev massMap (α : ℝ) (p : ℝ × ℝ) : ℂ := circleMap 0 (massRadius α p.1) p.2

lemma measurable_massMap (α : ℝ) : Measurable (massMap α) :=
  circleMap.continuous.measurable.comp
    (show Measurable (fun p : ℝ × ℝ ↦ (massRadius α p.1, p.2)) by unfold massRadius; fun_prop)

theorem weightedArea_eq_map_mass {α : ℝ} (hα : -1 < α) :
    weightedArea α = ((volume.restrict (openRadii)).prod angleMeasure).map (massMap α) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (measurable_massMap α), lintegral_prod (fun p ↦ g (massMap α p)) (hg.comp (measurable_massMap α)).aemeasurable]
  let H (r : ℝ) := ∫⁻ θ, g (circleMap 0 r θ) ∂angleMeasure
  change _ = ∫⁻ y in openRadii, H (massRadius α y)
  have hp : 0 < α + 1 := by linarith
  let ρ (r : ℝ) := 2 * r * ((α + 1) * (1 - r ^ 2) ^ α)
  have hρ {r : ℝ} (hr : r ∈ openRadii) : 0 < ρ r := by
    dsimp [ρ]; positivity [hr.1, radial_defect_pos (Ioo_subset_Ico_self hr)]
  have hd r (hr : r ∈ openRadii) : HasDerivWithinAt (radiusMass α) (-ρ r) (openRadii) r := by
    convert ((((hasDerivAt_pow 2 r).const_sub 1).rpow_const (p := α + 1)
      (Or.inl (radial_defect_pos (Ioo_subset_Ico_self hr)).ne')).hasDerivWithinAt) using 1
    dsimp [ρ]; ring_nf
  have img : radiusMass α '' openRadii = openRadii :=
    Subset.antisymm (image_subset_iff.mpr (fun _ ↦ radiusMass_mem_unit hα))
      (fun y hy ↦ ⟨massRadius α y, massRadius_mem_unit hα hy, massRadius_mass hα hy⟩)
  calc
    _ = ∫⁻ r in openRadii, ENNReal.ofReal (ρ r) * H r := by
      let P := fun p : ℝ × ℝ ↦ circleMap 0 p.1 p.2
      have hP : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) = P := by
        funext p; simp [P, circleMap, Complex.exp_mul_I]
      have hset : P ⁻¹' disk ∩ polarCoord.target = openRadii ×ˢ Ioo (-π) π := by
        ext p
        simp [polarCoord_target, openRadii, mem_disk_iff, P, abs_lt]
        grind
      have hd : MeasurableSet disk := Metric.isOpen_ball.measurableSet
      rw [weightedArea, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hg,
        diskArea, ← lintegral_indicator hd, area, lintegral_smul_measure,
        ← Complex.lintegral_comp_polarCoord_symm, hP]
      simp_rw [smul_eq_mul, ← indicator_comp_right]
      simp_rw [← indicator_mul_right _ (fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1), Function.comp_apply, Pi.mul_apply]
      rw [lintegral_indicator (hd.preimage circleMap.continuous.measurable),
        Measure.restrict_restrict (hd.preimage circleMap.continuous.measurable), hset,
        Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      simp only [angleMeasure, lintegral_smul_measure, smul_eq_mul, P, norm_circleMap_zero, abs_of_pos hr.1,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ρ, H]
      have hr0 : 0 < r := hr.1
      have hb := radial_defect_pos (Ioo_subset_Ico_self hr)
      simp (disch := first | positivity [hp, hr0, hb] | assumption) only [← mul_assoc, ← ENNReal.ofReal_mul]
      congr 2
      field_simp [pi_ne_zero]
    _ = _ := by
      conv_rhs => rw [← img]
      rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd
        ((show LeftInvOn (massRadius α) (radiusMass α) openRadii from fun _ ↦ mass_massRadius hα).injOn)]
      exact setLIntegral_congr_fun measurableSet_Ioo fun r hr ↦ by
        simp [abs_of_pos (hρ hr), mass_massRadius hα hr]

instance : IsProbabilityMeasure (volume.restrict openRadii) where
  measure_univ := by norm_num

theorem weightedArea_isProbabilityMeasure (α : ℝ) (hα : -1 < α) : IsProbabilityMeasure (weightedArea α) := by
  rw [weightedArea_eq_map_mass hα]
  exact instIsProbabilityMeasureMap

instance diskArea_isProbabilityMeasure : IsProbabilityMeasure diskArea :=
  weightedArea_zero ▸ weightedArea_isProbabilityMeasure 0 (by norm_num)

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weighted disk is the product of a uniform mass coordinate and uniform angle. -/
theorem integral_weightedArea_mass {α : ℝ} (hα : -1 < α) {f : ℂ → E}
    (hf : Integrable f (weightedArea α)) :
    (∫ z, f z ∂weightedArea α) = ∫ y in (0 : ℝ)..1, circleAverage f 0 (massRadius α y) := by
  rw [weightedArea_eq_map_mass hα] at hf ⊢
  have hi := hf.comp_aemeasurable (measurable_massMap α).aemeasurable
  simp_rw [circleAverage_eq_integral_angleMeasure]
  rw [intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_map (measurable_massMap α).aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ hi

theorem integral_diskArea_eq_circleAverage_sqrt_one_sub {f : ℂ → E} (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea = ∫ y in (0 : ℝ)..1, circleAverage f 0 (sqrt (1 - y)) := by
  rw [← weightedArea_zero] at hf ⊢
  simpa [massRadius] using (integral_weightedArea_mass (by norm_num : (-1 : ℝ) < 0) hf)

end
end BergmanWeakType
