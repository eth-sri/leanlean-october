/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.Module

@[expose] public section

noncomputable section

open Set MeasureTheory Metric
open scoped Real ENNReal

namespace BergmanWeakType

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Disk integration is twice the radius-weighted integral of circular means. -/
theorem integral_diskArea_eq_circleAverage [CompleteSpace E] {f : ℂ → E}
    (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea = ∫ r in Ioo (0 : ℝ) 1, (2 * r) • Real.circleAverage f 0 r := by
  have hfD : IntegrableOn f disk := by
    simp only [diskArea, area, Measure.restrict_smul] at hf
    exact (integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top).mp hf
  have hD : MeasurableSet disk := isOpen_ball.measurableSet
  have hfi : Integrable (disk.indicator f) := (integrable_indicator_iff hD).mpr hfD
  have hsource := (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable
    hfi).integrableOn (s := polarCoord.source)
  rw [← polarCoord.symm_image_target_eq_source] at hsource
  have hp : IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • disk.indicator f (Complex.polarCoord.symm p))
      polarCoord.target :=
    ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      polarCoord.open_target.measurableSet
      (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
      polarCoord.symm.injOn (disk.indicator f ∘ Complex.measurableEquivRealProd.symm)).mp
      hsource).congr ((ae_restrict_mem polarCoord.open_target.measurableSet).mono fun p hp ↦ by
        simp only [det_fderivPolarCoordSymm, Function.comp_apply,
          Complex.measurableEquivRealProd_symm_polarCoord_symm_apply,
          abs_of_pos (show 0 < p.1 from hp.1)])
  have hpolar : ∫ z in disk, f z = ∫ r in Ioo (0 : ℝ) 1, r •
      ∫ θ in Ioo (-π) π, f (Complex.polarCoord.symm (r, θ)) := by
    rw [← integral_indicator hD, ← Complex.integral_comp_polarCoord_symm]
    change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      p.1 • disk.indicator f (Complex.polarCoord.symm p)) = _
    rw [Measure.volume_eq_prod, setIntegral_prod _ hp,
      ← (by ext r; simp : Ioi (0 : ℝ) ∩ Iio 1 = Ioo 0 1),
      ← setIntegral_indicator measurableSet_Iio]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
    have hr0 : 0 < r := hr
    by_cases hr1 : r < 1
    · simp only [mem_Iio, hr1, indicator_of_mem, ← integral_smul]
      refine setIntegral_congr_fun measurableSet_Ioo fun θ _ ↦ ?_
      have hmem : Complex.polarCoord.symm (r, θ) ∈ disk := by
        simp only [disk, mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
          abs_of_pos hr0, hr1]
      simp only [indicator_of_mem hmem]
    · rw [indicator_of_notMem (show r ∉ Iio 1 from hr1)]
      exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun θ ↦ by
        have hnmem : Complex.polarCoord.symm (r, θ) ∉ disk := by
          simpa only [disk, mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
            abs_of_pos hr0] using hr1
        change r • disk.indicator f (Complex.polarCoord.symm (r, θ)) = 0
        rw [indicator_of_notMem hnmem, smul_zero])
  rw [diskArea, area, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ π⁻¹), hpolar, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioo fun r _ ↦ ?_
  have hangle : (∫ θ in Ioo (-π) π, f (Complex.polarCoord.symm (r, θ))) =
      (2 * π) • Real.circleAverage f 0 r := by
    rw [Real.circleAverage_eq_integral_add (-π),
      intervalIntegral.integral_comp_add_right (fun θ ↦ f (circleMap 0 r θ)) (-π), zero_add,
      show 2 * π + -π = π by ring, smul_smul, mul_inv_cancel₀ (by positivity : 2 * π ≠ 0),
      one_smul, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
    congr 1; funext θ; congr 1
    simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  rw [hangle, smul_smul, smul_smul]
  congr 1
  field_simp

theorem integral_weightedArea_eq_diskArea [CompleteSpace E] {α : ℝ} (hα : -1 < α)
    (f : ℂ → E) :
    ∫ z, f z ∂weightedArea α =
      ∫ z, ((α + 1) * (1 - ‖z‖ ^ 2) ^ α) • f z ∂diskArea := by
  rw [weightedArea, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  exact integral_congr_ae (ae_mem_disk.mono fun z hz ↦ by
    have h0 : 0 ≤ (α + 1) * (1 - ‖z‖ ^ 2) ^ α := mul_nonneg (by linarith)
      (Real.rpow_nonneg (by have := (mem_disk_iff z).mp hz; nlinarith [norm_nonneg z]) _)
    simp only [ENNReal.toReal_ofReal h0])

theorem integral_weightedArea_eq_circleAverage [CompleteSpace E] {α : ℝ} (hα : -1 < α)
    {f : ℂ → E} (hf : Integrable f (weightedArea α)) :
    ∫ z, f z ∂weightedArea α = ∫ r in Set.Ioo (0 : ℝ) 1,
      (2 * r * ((α + 1) * (1 - r ^ 2) ^ α)) • Real.circleAverage f 0 r := by
  have hfi : Integrable (fun z ↦ ((α + 1) * (1 - ‖z‖ ^ 2) ^ α) • f z) diskArea :=
    ((integrable_withDensity_iff_integrable_smul'
      (by fun_prop : Measurable (fun z : ℂ ↦ ENNReal.ofReal ((α + 1) * (1 - ‖z‖ ^ 2) ^ α)))
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hf).congr
      (ae_mem_disk.mono fun z hz ↦ by
        have h0 : 0 ≤ (α + 1) * (1 - ‖z‖ ^ 2) ^ α := mul_nonneg (by linarith)
          (Real.rpow_nonneg (by have := (mem_disk_iff z).mp hz; nlinarith [norm_nonneg z]) _)
        simp only [ENNReal.toReal_ofReal h0])
  rw [integral_weightedArea_eq_diskArea hα, integral_diskArea_eq_circleAverage hfi]
  refine setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ ?_
  rw [mul_smul (2 * r)]
  congr 1
  rw [← Real.circleAverage_fun_smul]
  refine Real.circleAverage_congr_sphere fun z hz ↦ ?_
  rw [show ‖z‖ = r by simpa [abs_of_pos hr.1] using hz]

end BergmanWeakType
