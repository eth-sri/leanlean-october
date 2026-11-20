/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.PolarCap
public import BergmanWeakType.Weighted.RadialLevel
public import BergmanWeakType.Weighted.AnnularSharpness
public import BergmanWeakType.Boundary.Concentration

/-! # Sharp positive weighted constants and the complex weighted upper bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace BergmanWeakType

open Weighted

/-- After disintegration in exterior mass, the normalized cap estimate bounds
exactly the product measure of the weak level set. -/
private theorem source_bound (ν : PolarSource) [IsFiniteMeasure ν] {α t : ℝ} (hα : -1 < α) (ht : 0 < t) :
    ENNReal.ofReal t * weightedArea α {z | t < ν.potential α z} ≤ ENNReal.ofReal (gammaConstant α) * ENNReal.ofReal (ν.potential α 0) := by
  let := weightedArea_isProbabilityMeasure α hα
  let E := {z | t < ν.potential α z}
  have me : MeasurableSet E := measurableSet_lt measurable_const (ν.measurable_potential α)
  let U y θ := ν.potential α (sample (y,θ)) / normalizer α y
  let s := t / gammaConstant α
  have hγ := gammaConstant_pos hα
  have hs  := div_pos ht hγ
  have H := moving_cap_bound angleMeasure hα (U := U) (fun y ↦ ((ν.measurable_potential α).comp (by fun_prop)).div_const _)
    (fun y _ ↦ div_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (normalizer_nonneg ..)) hs.le (measurable_sample me) ?sub (normalized_cap_anti ν α)
  case sub =>
    intro y hy θ hz
    have h : exteriorMass α y * normalizer α y ≤ gammaConstant α := radialMass_mul_normalizer_le hα hy.1 hy.2
    apply (le_div_iff₀ (normalizer_pos α hy)).mpr
    calc
      _ ≤ s * gammaConstant α := by nlinarith
      _ ≤ _ := by simpa [s,hγ.ne'] using hz.le
  have hi : s * (weightedArea α).real E ≤ ν.potential α 0 := by
    conv_lhs => rw [measureReal_def,weightedArea_map hα,Measure.map_apply measurable_sample me]
    apply H.trans
    simp [capMean, U, sample]
  have hreal := (div_le_iff₀ hγ).mp (show t * (weightedArea α).real E / gammaConstant α ≤ _ by
    simpa [s,div_mul_eq_mul_div] using hi)
  simpa [mul_comm _ (gammaConstant α), ENNReal.ofReal_mul ht.le, ENNReal.ofReal_mul hγ.le] using ENNReal.ofReal_le_ofReal hreal

theorem isWeakTypeBound_weightedPositiveProjection {α : ℝ} (hα : -1 < α) :
    IsWeakTypeBound (weightedArea α) (weightedPositiveProjection α) (ENNReal.ofReal (gammaConstant α)) := by
  intro f hf t ht
  let μ := (weightedArea α).withDensity fun w ↦ ‖f w‖ₑ
  let := isFiniteMeasure_withDensity hf.hasFiniteIntegral.ne
  let ν : PolarSource := μ.comap Subtype.val
  have hs : ∀ᵐ w ∂μ, w ∈ ClosedDisk := (withDensity_absolutelyContinuous _ _).ae_le
    ((ae_mem_disk_weightedArea α).mono fun _ hw ↦ Metric.ball_subset_closedBall hw)
  have eq z (hz : z ∈ disk) : ENNReal.ofReal (ν.potential α z) = weightedPositiveProjection α f z := by
    have hi : Integrable (fun w ↦ ‖weightedKernel α z w‖) μ := integrable_on_support (isCompact_closedBall _ _) hs ((kernel_continuous α).norm.comp
      (f := fun w ↦ (z,w)) (by fun_prop) (fun w hw ↦ ⟨hz,hw⟩))
    rw [PolarSource.potential, integral_subtype_comap Metric.isClosed_closedBall.measurableSet
      (fun w ↦ ‖weightedKernel α z w‖), Measure.restrict_eq_self_of_ae_mem hs,
      ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun _ ↦ norm_nonneg _), weightedPositiveProjection,
      lintegral_withDensity_eq_lintegral_mul₀ hf.aemeasurable.enorm (by measurability)]
    simp [mul_comm]
  have h := source_bound ν hα ht
  rw [eq 0 (by simp)] at h
  rw [← show weightedArea α {z | t < ν.potential α z} = _ from measure_congr ((ae_mem_disk_weightedArea α).mono (by grind [ENNReal.ofReal_lt_ofReal_iff_of_nonneg]))]
  simpa [weightedPositiveProjection] using h

theorem weightedPositiveProjection_constant_eq (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (weightedPositiveProjection α) =
      ENNReal.ofReal (gammaConstant α) :=
  le_antisymm (sInf_le (isWeakTypeBound_weightedPositiveProjection hα))
    (gammaConstant_le_weightedPositiveProjection_constant α hα)

theorem weightedProjection_constant_le (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) ≤
      ENNReal.ofReal (gammaConstant α) := sInf_le
    (isWeakTypeBound_mono (enorm_weightedProjection_le_weightedPositiveProjection α) (isWeakTypeBound_weightedPositiveProjection hα))


theorem positiveProjection_constant_eq_one : weakTypeConstant diskArea positiveProjection = 1 := by
  simpa using weightedPositiveProjection_constant_eq 0 (by norm_num)

theorem projection_constant_eq_one :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) = 1 := le_antisymm (by simpa using weightedProjection_constant_le 0 (by norm_num))
    (by simpa using one_le_weightedProjection_constant 0 (by norm_num))

end BergmanWeakType
