/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Notation

public import BergmanWeakType.Definitions
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Normalization and support of Bergman area measures -/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

theorem area_ball (c : ℂ) (r : ℝ) : area (Metric.ball c r) = ENNReal.ofReal r ^ 2 := by
  rw [area, Measure.smul_apply, smul_eq_mul, Complex.volume_ball]
  rw [ENNReal.ofReal_inv_of_pos Real.pi_pos, ← NNReal.coe_real_pi,
    ENNReal.ofReal_coe_nnreal]
  rw [mul_left_comm,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero) ENNReal.coe_ne_top,
    mul_one]

theorem area_closedBall (c : ℂ) (r : ℝ) :
    area (Metric.closedBall c r) = ENNReal.ofReal r ^ 2 := by
  rw [area, Measure.smul_apply, smul_eq_mul, Complex.volume_closedBall]
  rw [ENNReal.ofReal_inv_of_pos Real.pi_pos, ← NNReal.coe_real_pi,
    ENNReal.ofReal_coe_nnreal]
  rw [mul_left_comm,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero) ENNReal.coe_ne_top,
    mul_one]

theorem area_disk : area disk = 1 := by
  simpa [disk] using area_ball 0 1

instance diskArea_isProbabilityMeasure : IsProbabilityMeasure diskArea where
  measure_univ := by simpa [diskArea] using area_disk

theorem ae_mem_disk : ∀ᵐ z ∂diskArea, z ∈ disk :=
  ae_restrict_mem Metric.isOpen_ball.measurableSet

theorem ae_mem_disk_weightedArea (α : ℝ) : ∀ᵐ z ∂weightedArea α, z ∈ disk := by
  exact (withDensity_absolutelyContinuous diskArea _).ae_le ae_mem_disk

/-- Under normalized disk area, the squared radius is uniform on the unit interval. -/
theorem map_norm_sq_diskArea :
    diskArea.map (fun z : ℂ ↦ ‖z‖ ^ 2) = volume.restrict (Icc01) := by
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
    · have hsub : Metric.closedBall (0 : ℂ) (Real.sqrt t) ⊆ disk := by
        intro z hz
        exact lt_of_le_of_lt hz ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
          (by simpa using ht1))
      rw [diskArea, Measure.restrict_eq_self _ hsub, area_closedBall,
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg t), Real.sq_sqrt ht,
        Measure.restrict_apply measurableSet_Iic]
      have hset : Set.Iic t ∩ Icc01 = Set.Icc 0 t := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨hxt, hx0, _⟩
          exact ⟨hx0, hxt⟩
        · rintro ⟨hx0, hxt⟩
          exact ⟨hxt, hx0, hxt.trans ht1.le⟩
      simp [hset]
    · have hsub : disk ⊆ Metric.closedBall (0 : ℂ) (Real.sqrt t) := by
        intro z hz
        exact le_trans (le_of_lt hz) ((Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) ht).2
          (by simpa using le_of_not_gt ht1))
      rw [diskArea, Measure.restrict_apply_superset hsub, area_disk,
        Measure.restrict_apply_superset (Set.Icc_subset_Iic_self.trans
          (Set.Iic_subset_Iic.mpr (le_of_not_gt ht1)))]
      simp
  · have hpre : (fun z : ℂ ↦ ‖z‖ ^ 2) ⁻¹' Set.Iic t = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr ((lt_of_not_ge ht).trans_le (sq_nonneg ‖z‖))
    rw [hpre, measure_empty, Measure.restrict_apply measurableSet_Iic]
    have hset : Set.Iic t ∩ Icc01 = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hxt hx0 _
      exact ht (hx0.trans hxt)
    simp [hset]

/-- Exact weighted mass of the exterior of a circle. -/
theorem weightedArea_norm_gt {α r : ℝ} (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    weightedArea α {z : ℂ | r < ‖z‖} = ENNReal.ofReal ((1 - r ^ 2) ^ (α + 1)) := by
  have hr₂ : r ^ 2 < 1 := by nlinarith
  have hpre : {z : ℂ | r < ‖z‖} =
      (fun z : ℂ ↦ ‖z‖ ^ 2) ⁻¹' Set.Ioi (r ^ 2) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi]
    exact (sq_lt_sq₀ hr (norm_nonneg z)).symm
  have hm : Measurable (fun u : ℝ ↦ ENNReal.ofReal ((α + 1) * (1 - u) ^ α)) := by
    fun_prop
  rw [hpre, weightedArea, withDensity_apply _ (measurableSet_Ioi.preimage (by fun_prop)),
    ← setLIntegral_map measurableSet_Ioi hm (by fun_prop : Measurable (fun z : ℂ ↦ ‖z‖ ^ 2)),
    map_norm_sq_diskArea, Measure.restrict_restrict measurableSet_Ioi]
  have hset : Set.Ioi (r ^ 2) ∩ Icc01 = Set.Ioc (r ^ 2) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hx, _, hx1⟩
      exact ⟨hx, hx1⟩
    · rintro ⟨hx, hx1⟩
      exact ⟨hx, (sq_nonneg r).trans hx.le, hx1⟩
  rw [hset]
  have hf : IntervalIntegrable (fun u : ℝ ↦ (1 - u) ^ α) volume (r ^ 2) 1 := by
    convert! ((intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := 1 - r ^ 2) hα).comp_sub_left 1).symm using 1 <;> ring
  have hfi : IntegrableOn (fun u : ℝ ↦ (α + 1) * (1 - u) ^ α) (Set.Ioc (r ^ 2) 1) :=
    (hf.const_mul (α + 1)).1
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (r ^ 2) 1)]
      (fun u : ℝ ↦ (α + 1) * (1 - u) ^ α) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnonneg,
    ← intervalIntegral.integral_of_le hr₂.le, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ α) 1]
  simp only [sub_self]
  rw [integral_rpow (Or.inl hα)]
  have hpos : 0 < α + 1 := by linarith
  simp only [Real.zero_rpow hpos.ne', sub_zero]
  rw [mul_div_cancel₀ _ hpos.ne']

/-- The radial weight is normalized for every admissible exponent. -/
theorem weightedArea_univ (α : ℝ) (hα : -1 < α) : weightedArea α Set.univ = 1 := by
  have hsingle : weightedArea α {0} = 0 := by
    simp [weightedArea, diskArea, area, lintegral_singleton]
  have h : weightedArea α (Set.univ \ {0}) = 1 := by
    have h := weightedArea_norm_gt hα le_rfl zero_lt_one
    have hset : {z : ℂ | 0 < ‖z‖} = Set.univ \ {0} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_univ, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨trivial, fun h0 => by simp [h0] at h⟩, fun h => norm_pos_iff.mpr h.2⟩
    rw [hset] at h
    simpa using h
  rw [show (Set.univ : Set ℂ) = (Set.univ \ {0}) ∪ {0} by ext z; simp,
    measure_union (by simp [Set.disjoint_left]) (measurableSet_singleton 0), hsingle, h, add_zero]

theorem weightedArea_isProbabilityMeasure (α : ℝ) (hα : -1 < α) :
    IsProbabilityMeasure (weightedArea α) :=
  ⟨weightedArea_univ α hα⟩

theorem diskArea_absolutelyContinuous_weightedArea (α : ℝ) (hα : -1 < α) :
    diskArea ≪ weightedArea α := by
  apply withDensity_absolutelyContinuous'
  · fun_prop
  · filter_upwards [ae_mem_disk] with z hz
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply mul_pos (by linarith)
    apply Real.rpow_pos_of_pos
    have hz_norm : ‖z‖ < 1 := by simpa [disk] using hz
    nlinarith [norm_nonneg z]

end BergmanWeakType
