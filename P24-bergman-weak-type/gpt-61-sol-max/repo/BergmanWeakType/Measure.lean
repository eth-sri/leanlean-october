/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Rigidity.PolarIntegral
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Normalization and support of Bergman area measures -/




open MeasureTheory


namespace BergmanWeakType

instance area_isAddHaarMeasure : Measure.IsAddHaarMeasure area :=
  Measure.IsAddHaarMeasure.smul volume (by positivity) ENNReal.ofReal_ne_top

instance diskArea_isProbabilityMeasure : IsProbabilityMeasure diskArea where
  measure_univ := by
    simp [diskArea, area, disk, Complex.volume_ball,
      ENNReal.ofReal_inv_of_pos Real.pi_pos]
    simp [← NNReal.coe_real_pi, ENNReal.inv_mul_cancel, NNReal.pi_ne_zero]

theorem ae_mem_disk : ∀ᵐ z ∂diskArea, z ∈ disk :=
  ae_restrict_mem Metric.isOpen_ball.measurableSet

theorem ae_mem_disk_weightedArea (α : ℝ) : ∀ᵐ z ∂weightedArea α, z ∈ disk := (withDensity_absolutelyContinuous diskArea _).ae_le ae_mem_disk

/-- Under normalized disk area, the squared radius is uniform on the unit interval. -/
theorem map_norm_sq_diskArea : diskArea.map (fun z : ℂ ↦ ‖z‖ ^ 2) = volume.restrict unitInterval :=
  by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map (by fun_prop) (by fun_prop)]
  have hi : Integrable (fun z : ℂ ↦ F _) diskArea :=
    (F.integrable (μ := diskArea.map (fun z : ℂ ↦ ‖z‖ ^ 2))).comp_measurable (by fun_prop)
  rw [integral_diskArea_eq_circleAverage_sqrt hi]
  rw [integral_Icc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y hy
  apply Real.circleAverage_const_on_circle
  intro z hz
  rw [show ‖z‖ = |Real.sqrt y| by simp_all, sq_abs, Real.sq_sqrt hy.1.le]

theorem weightedArea_norm_gt {α r : ℝ}  (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    weightedArea α {z : ℂ | r < ‖z‖} = ENNReal.ofReal ((1 - r ^ 2) ^ (α + 1)) := by
  have hr₂ : r ^ 2 < 1 := by nlinarith
  have hpre : {z : ℂ | r < ‖z‖} =
      (fun z : ℂ ↦ ‖z‖ ^ 2) ⁻¹' Set.Ioi (r ^ 2) := by
    ext z
    exact (sq_lt_sq₀ hr (norm_nonneg z)).symm
  have hm : Measurable (fun u : ℝ ↦ ENNReal.ofReal ((α + 1) * (1 - u) ^ α)) := by
    fun_prop
  rw [hpre, weightedArea, withDensity_apply _ (measurableSet_Ioi.preimage (by fun_prop)),
    ← setLIntegral_map measurableSet_Ioi hm (by fun_prop ),
    map_norm_sq_diskArea, Measure.restrict_restrict measurableSet_Ioi]
  have hset : Set.Ioi (r ^ 2) ∩ unitInterval = Set.Ioc (r ^ 2) 1 := by
    grind [sq_nonneg r]
  rw [hset]
  have hf : IntervalIntegrable (fun u : ℝ ↦ (1 - u) ^ α) volume (r ^ 2) 1 := by
    convert! ((intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := 1 - r ^ 2) hα).comp_sub_left 1).symm using 1 <;> ring
  rw [← ofReal_integral_eq_lintegral_ofReal ((hf.const_mul (α + 1)).1) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _)
  ),
    ← intervalIntegral.integral_of_le hr₂.le, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ α) 1]
  simp
  rw [integral_rpow (Or.inl hα)]
  have hpos := neg_lt_iff_pos_add.mp hα
  simp [Real.zero_rpow hpos.ne']
  grind

/-- The admissible radial weight defines a probability measure. -/
theorem weightedArea_isProbabilityMeasure (α : ℝ) (hα : -1 < α) : IsProbabilityMeasure (weightedArea α) where
  measure_univ := by
    have h := weightedArea_norm_gt  hα le_rfl zero_lt_one
    rw [show {z : ℂ | 0 < ‖z‖} = {0}ᶜ by continuity,
      measure_of_measure_compl_eq_zero (by simp [weightedArea, diskArea])] at h
    simp_all

instance weightedArea_isFiniteMeasure (α : ℝ) : IsFiniteMeasure (weightedArea α) := by
  by_cases h : -1 < α
  · let := weightedArea_isProbabilityMeasure α h
    infer_instance
  · have hz : weightedArea α = 0 := by
      rw [weightedArea, withDensity_eq_zero_iff (by fun_prop)]
      filter_upwards [ae_mem_disk] with z hz
      apply ENNReal.ofReal_eq_zero.mpr
      apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
      apply Real.rpow_nonneg
      have  := by simpa [disk] using! hz
      nlinarith [norm_nonneg z]
    rw [hz]
    infer_instance

/-- The admissible radial weights have the same null sets as disk area. -/
theorem diskArea_absolutelyContinuous_weightedArea (α : ℝ) (hα : -1 < α) :
    diskArea ≪ weightedArea α := by
  apply withDensity_absolutelyContinuous'
  · fun_prop
  · filter_upwards [ae_mem_disk] with z hz
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply mul_pos (by linarith)
    apply Real.rpow_pos_of_pos
    have hz_norm : ‖z‖ < 1 := by exact?
    simp_all


end BergmanWeakType
