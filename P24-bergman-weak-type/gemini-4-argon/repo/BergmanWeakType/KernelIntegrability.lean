/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

/-- Pointwise domination orders the optimal weak type constants. -/
theorem weakTypeConstant_mono {μ : Measure ℂ} {T S : (ℂ → ℂ) → ℂ → ℝ≥0∞}
    (h : ∀ f, Integrable f μ → ∀ z, T f z ≤ S f z) :
    weakTypeConstant μ T ≤ weakTypeConstant μ S :=
  le_sInf fun _ hC ↦ sInf_le fun f hf t ht ↦
    (mul_le_mul_right (measure_mono fun z hz ↦ hz.trans_le (h f hf z)) _).trans (hC f hf t ht)

theorem area_ball (c : ℂ) (r : ℝ) : area (Metric.ball c r) = ENNReal.ofReal r ^ 2 := by
  rw [area, Measure.smul_apply, smul_eq_mul, Complex.volume_ball,
    ENNReal.ofReal_inv_of_pos Real.pi_pos, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal,
    mul_left_comm, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero)
      ENNReal.coe_ne_top, mul_one]

instance diskArea_isProbabilityMeasure : IsProbabilityMeasure diskArea where
  measure_univ := by simpa [diskArea, disk] using area_ball 0 1

theorem ae_mem_disk : ∀ᵐ z ∂diskArea, z ∈ disk :=
  ae_restrict_mem Metric.isOpen_ball.measurableSet

theorem ae_mem_disk_weightedArea (α : ℝ) : ∀ᵐ z ∂weightedArea α, z ∈ disk :=
  (withDensity_absolutelyContinuous diskArea _).ae_le ae_mem_disk

/-- Under normalized disk area, the squared radius is uniform on the unit interval. -/
theorem map_norm_sq_diskArea :
    diskArea.map (fun z : ℂ ↦ ‖z‖ ^ 2) = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (by fun_prop : Measurable (fun z : ℂ ↦ ‖z‖ ^ 2)) measurableSet_Iic]
  by_cases ht : 0 ≤ t
  · have hpre : (fun z : ℂ ↦ ‖z‖ ^ 2) ⁻¹' Set.Iic t =
        Metric.closedBall (0 : ℂ) (Real.sqrt t) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, Metric.mem_closedBall, dist_zero_right]
      exact (Real.le_sqrt (norm_nonneg z) ht).symm
    rw [hpre]
    by_cases ht1 : t < 1
    · have hsub : Metric.closedBall (0 : ℂ) (Real.sqrt t) ⊆ disk := fun z hz ↦
        lt_of_le_of_lt hz ((Real.sqrt_lt' zero_lt_one).2 (by simpa using ht1))
      have hcb : area (Metric.closedBall (0 : ℂ) (Real.sqrt t)) = ENNReal.ofReal t := by
        rw [area, Measure.smul_apply, smul_eq_mul, Complex.volume_closedBall,
          ENNReal.ofReal_inv_of_pos Real.pi_pos, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal,
          mul_left_comm, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero)
            ENNReal.coe_ne_top, mul_one, ← ENNReal.ofReal_pow (Real.sqrt_nonneg t), Real.sq_sqrt ht]
      rw [diskArea, Measure.restrict_eq_self _ hsub, hcb,
        Measure.restrict_apply measurableSet_Iic]
      have hset : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 t := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        exact ⟨fun h ↦ ⟨h.2.1, h.1⟩, fun h ↦ ⟨h.2, h.1, h.2.trans ht1.le⟩⟩
      simp [hset]
    · have hsub : disk ⊆ Metric.closedBall (0 : ℂ) (Real.sqrt t) := fun z hz ↦
        le_trans (le_of_lt hz) ((Real.le_sqrt zero_le_one ht).2 (by simpa using le_of_not_gt ht1))
      rw [diskArea, Measure.restrict_apply_superset hsub,
        show area disk = 1 by simpa [disk] using area_ball 0 1,
        Measure.restrict_apply_superset (Set.Icc_subset_Iic_self.trans
          (Set.Iic_subset_Iic.mpr (le_of_not_gt ht1)))]
      simp
  · have hpre : (fun z : ℂ ↦ ‖z‖ ^ 2) ⁻¹' Set.Iic t = ∅ :=
      Set.eq_empty_of_forall_notMem fun z hz ↦
        not_le.mpr ((lt_of_not_ge ht).trans_le (sq_nonneg ‖z‖)) hz
    have hset : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx ↦ ht (hx.2.1.trans hx.1)
    rw [hpre, measure_empty, Measure.restrict_apply measurableSet_Iic, hset, measure_empty]

theorem weightedArea_isProbabilityMeasure (α : ℝ) (hα : -1 < α) :
    IsProbabilityMeasure (weightedArea α) := ⟨by
  rw [weightedArea, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hm : Measurable (fun u : ℝ ↦ ENNReal.ofReal ((α + 1) * (1 - u) ^ α)) := by fun_prop
  rw [← lintegral_map hm (by fun_prop : Measurable (fun z : ℂ ↦ ‖z‖ ^ 2)),
    map_norm_sq_diskArea]
  have hf : IntervalIntegrable (fun u : ℝ ↦ (1 - u) ^ α) volume 0 1 := by
    simpa using
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hα).comp_sub_left 1).symm
  have hfi : IntegrableOn (fun u : ℝ ↦ (α + 1) * (1 - u) ^ α) (Set.Icc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp (hf.const_mul (α + 1))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun u : ℝ ↦ (α + 1) * (1 - u) ^ α) :=
    (ae_restrict_mem measurableSet_Icc).mono fun u hu ↦
      mul_nonneg (by linarith) (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnonneg, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ α) 1]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl hα)]
  have hpos : 0 < α + 1 := by linarith
  simp [Real.zero_rpow hpos.ne', ne_of_gt hpos]⟩

/-- The admissible radial weights have the same null sets as disk area. -/
theorem diskArea_absolutelyContinuous_weightedArea (α : ℝ) (hα : -1 < α) :
    diskArea ≪ weightedArea α := by
  refine withDensity_absolutelyContinuous' (by fun_prop) (ae_mem_disk.mono fun z hz ↦ ?_)
  have hz_norm : ‖z‖ < 1 := by simpa [disk] using hz
  exact (ENNReal.ofReal_pos.mpr (mul_pos (by linarith)
    (Real.rpow_pos_of_pos (by nlinarith [norm_nonneg z]) _))).ne'

@[simp]
theorem mem_disk_iff (z : ℂ) : z ∈ disk ↔ ‖z‖ < 1 := by
  simp [disk, Metric.mem_ball, dist_zero_right]

theorem kernel_denominator_ne_zero {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    1 - z * star w ≠ 0 := fun h ↦ by
  have hmul : ‖z * star w‖ < 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_right (norm_nonneg z) ((mem_disk_iff w).mp hw).le).trans_lt
      ((mem_disk_iff z).mp hz)
  rw [(sub_eq_zero.mp h).symm, norm_one] at hmul
  exact lt_irrefl 1 hmul

@[simp]
theorem norm_kernel (z w : ℂ) : ‖kernel z w‖ = ‖1 - z * star w‖⁻¹ ^ 2 := by
  simp [kernel, norm_pow, norm_inv]

@[simp]
theorem norm_weightedKernel (α : ℝ) (z w : ℂ) :
    ‖weightedKernel α z w‖ = ‖1 - z * star w‖ ^ (-(α + 2)) := by
  simpa [weightedKernel] using Complex.norm_cpow_real (1 - z * star w) (-(α + 2))

@[simp]
theorem weightedKernel_zero (z w : ℂ) : weightedKernel 0 z w = kernel z w := by
  simp [weightedKernel, kernel, Complex.cpow_neg, ← inv_pow]

@[simp]
theorem weightedArea_zero : weightedArea 0 = diskArea := by
  simp [weightedArea]

@[simp]
theorem weightedPositiveProjection_zero (f : ℂ → ℂ) :
    weightedPositiveProjection 0 f = positiveProjection f := by
  funext z; simp [weightedPositiveProjection, positiveProjection]

@[simp]
theorem gammaConstant_zero : gammaConstant 0 = 1 := by
  simp [gammaConstant]

theorem gammaConstant_pos {α : ℝ} (hα : -1 < α) : 0 < gammaConstant α :=
  div_pos (Real.Gamma_pos_of_pos (by linarith)) (sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)))

theorem measurableSet_disk : MeasurableSet disk := Metric.isOpen_ball.measurableSet

/-- A fixed interior output point keeps the kernel denominator uniformly away from zero. -/
theorem kernel_denominator_norm_lower (z : ℂ) {w : ℂ} (hw : w ∈ disk) :
    1 - ‖z‖ ≤ ‖1 - z * star w‖ := by
  have hmul : ‖z * star w‖ ≤ ‖z‖ := by
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg z) ((mem_disk_iff w).mp hw).le
  exact (sub_le_sub_left hmul 1).trans (by simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) _)

theorem norm_kernel_le {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    ‖kernel z w‖ ≤ (1 - ‖z‖)⁻¹ ^ 2 := by
  rw [norm_kernel]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
    (inv_anti₀ (sub_pos.mpr ((mem_disk_iff z).mp hz))
      (kernel_denominator_norm_lower z hw)) 2

/-- The principal-power kernel is continuous throughout the input disk. -/
theorem continuousOn_weightedKernel (α : ℝ) {z : ℂ} (hz : z ∈ disk) :
    ContinuousOn (weightedKernel α z) disk :=
  (continuous_const.sub (continuous_const.mul continuous_star)).continuousOn.cpow_const
    fun w hw ↦ Complex.mem_slitPlane_iff.mpr (Or.inl <| by
      have hmul : ‖z * star w‖ < 1 := by
        rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_right (norm_nonneg z) ((mem_disk_iff w).mp hw).le).trans_lt
          ((mem_disk_iff z).mp hz)
      simpa only [Pi.sub_apply, Pi.mul_apply, Complex.sub_re, Complex.one_re] using
        sub_pos.mpr ((Complex.re_le_norm _).trans_lt hmul))

theorem aestronglyMeasurable_kernel {z : ℂ} (hz : z ∈ disk) :
    AEStronglyMeasurable (kernel z) diskArea := by
  have h := continuousOn_weightedKernel 0 hz
  change ContinuousOn (fun w ↦ weightedKernel 0 z w) disk at h
  exact (by simpa only [weightedKernel_zero] using h :
    ContinuousOn (kernel z) disk).aestronglyMeasurable measurableSet_disk

/-- Every admissible input gives an integrable unweighted kernel integrand at an interior point. -/
theorem integrable_kernel_mul {f : ℂ → ℂ} (hf : Integrable f diskArea) {z : ℂ}
    (hz : z ∈ disk) : Integrable (fun w ↦ kernel z w * f w) diskArea :=
  hf.bdd_mul (aestronglyMeasurable_kernel hz) (ae_mem_disk.mono fun _ hw ↦ norm_kernel_le hz hw)

/-- Every admissible input gives an integrable weighted kernel integrand at an interior point. -/
theorem integrable_weightedKernel_mul {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) {z : ℂ} (hz : z ∈ disk) :
    Integrable (fun w ↦ weightedKernel α z w * f w) (weightedArea α) :=
  hf.bdd_mul (((continuousOn_weightedKernel α hz).aestronglyMeasurable
    (μ := area) measurableSet_disk).mono_ac (withDensity_absolutelyContinuous diskArea _))
    ((ae_mem_disk_weightedArea α).mono fun _ hw ↦ by
      rw [norm_weightedKernel]
      exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr ((mem_disk_iff z).mp hz))
        (kernel_denominator_norm_lower z hw) (by linarith))

theorem weightedPositiveProjection_lt_top {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) {z : ℂ} (hz : z ∈ disk) :
    weightedPositiveProjection α f z < ∞ := by
  simpa only [weightedPositiveProjection, enorm_mul, ofReal_norm] using
    (hasFiniteIntegral_iff_enorm.mp
      (integrable_weightedKernel_mul hα hf hz).hasFiniteIntegral)

end BergmanWeakType
