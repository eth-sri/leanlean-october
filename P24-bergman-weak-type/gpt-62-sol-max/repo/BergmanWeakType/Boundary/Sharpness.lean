/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Boundary.Concentration
public import BergmanWeakType.Weighted.Normalizer
public import BergmanWeakType.Weighted.MassCoordinate
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The mass of small caps at the boundary of the disk -/

public section

open MeasureTheory Set Real Filter

namespace BergmanWeakType


/-- The limiting density after blowing up a boundary cap at the point one. -/
noncomputable def capProfile (α R : ℝ) (z : ℂ) : ℝ :=
  max (2 * z.re - R * ‖z‖ ^ 2) 0 ^ α

theorem continuous_capProfile {α : ℝ} (hα : 0 ≤ α) :
    Continuous (fun p : ℝ × ℂ ↦ capProfile α p.1 p.2) := by
  unfold capProfile
  fun_prop (disch := positivity)

theorem circleAverage_halfDiskPower {α : ℝ} (hα : 0 < α) {r : ℝ} (hr : 0 < r) :
    circleAverage (capProfile α 0) 0 r = r ^ α * gammaConstant α / 2 := by
  rw [circleAverage_eq_integral_add (-(π / 2)), smul_eq_mul,
    intervalIntegral.integral_of_le two_pi_pos.le, integral_Ioc_eq_integral_Ioo]
  have he : (∫ θ in Ioo (0 : ℝ) (2 * π), capProfile α 0 (circleMap 0 r (θ + -(π / 2)))) =
      (2 * r) ^ α * ∫ θ in Ioo (0 : ℝ) π, sin θ ^ α := by
    have hs : Ioo (0 : ℝ) π ⊆ Ioo 0 (2 * π) := Ioo_subset_Ioo_right (by linarith [pi_pos])
    rw [← integral_const_mul, ← Measure.restrict_restrict_of_subset hs, ← integral_indicator (μ := volume.restrict (Ioo 0 (2 * π))) measurableSet_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro θ hθ
    simp only [capProfile, zero_mul, sub_zero, circleMap_zero_re, ← sub_eq_add_neg, cos_sub_pi_div_two,
      ← mul_assoc]
    by_cases h : θ ∈ Ioo (0 : ℝ) π
    · have hp := sin_pos_of_pos_of_lt_pi h.1 h.2
      rw [indicator_of_mem h, max_eq_left (mul_nonneg (by positivity) hp.le), mul_rpow (by positivity) hp.le]
    · have hs : sin θ ≤ 0 := by
        rw [← sin_sub_two_pi θ]
        apply sin_nonpos_of_nonpos_of_neg_pi_le
        · linarith [hθ.2]
        grind
      rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos (by positivity) hs), zero_rpow hα.ne', indicator_of_notMem h]
  rw [he, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le pi_pos.le,
    mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le, gammaConstant_eq_sineIntegral (by linarith : -1 < α)]
  ring

theorem integral_halfDiskPower {α : ℝ} (hα : 0 < α) :
    (∫ z, capProfile α 0 z ∂diskArea) = gammaConstant α / (α + 2) := by
  have hi : Integrable (capProfile α 0) diskArea :=
    ((continuous_capProfile hα.le).comp (continuous_const.prodMk continuous_id)).continuousOn
      |>.integrableOn_compact (isCompact_closedBall 0 1) |>.mono_set Metric.ball_subset_closedBall
  rw [integral_diskArea_eq_circleAverage_sqrt_one_sub hi]
  calc
    _ = (gammaConstant α / 2) * ∫ y in (0 : ℝ)..1, (1 - y) ^ (α / 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro y hy
      dsimp only
      rw [circleAverage_halfDiskPower hα (sqrt_pos.mpr (sub_pos.mpr hy.2)),
        sqrt_eq_rpow, ← rpow_mul (sub_nonneg.mpr hy.2.le), show (1 / 2 : ℝ) * α = α / 2 by ring]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ (α / 2)) 1,
        sub_self, sub_zero, integral_rpow (Or.inl (by linarith))]
      simp only [one_rpow, zero_rpow (show α / 2 + 1 ≠ 0 by linarith), sub_zero]
      field_simp

private theorem weightedArea_boundaryCap_rescaled {α R : ℝ} (hα : 0 < α) (hR : 0 < R) :
    R ^ (-(α + 2)) * (weightedArea α).real (disk ∩ Metric.ball 1 R) =
      (α + 1) * ∫ u, capProfile α R u ∂diskArea := by
  let f := fun z : ℂ ↦ max (1 - ‖z‖ ^ 2) 0 ^ α
  have hm : Measurable f := by unfold f; fun_prop
  have hn (z : ℂ) : 0 ≤ (α + 1) * f z := by positivity
  have hμ : weightedArea α = area.withDensity (fun z ↦ ENNReal.ofReal ((α + 1) * f z)) := by
    rw [weightedArea, diskArea, ← withDensity_indicator measurableSet_disk]
    congr 1
    ext z
    have h : z ∈ disk ↔ 0 < 1 - ‖z‖ ^ 2 := by simp [mem_disk_iff]
    by_cases hz : z ∈ disk
    · simp [hz, f, max_eq_left ((h.mp hz).le)]
    · simp [hz, f, max_eq_right (le_of_not_gt (mt h.mpr hz)), zero_rpow hα.ne']
  let e := diskChart 1 (neg_ne_zero.mpr hR.ne')
  have he : area.restrict (Metric.ball 1 R) = ENNReal.ofReal (R ^ 2) • Measure.map e diskArea := by
    simpa [abs_of_pos hR, e] using area_restrict_ball_eq_map 1 (neg_ne_zero.mpr hR.ne')
  have eq (u : ℂ) : f (e u) = R ^ α * capProfile α R u := by
    change max (1 - ‖1 + ((-R : ℝ) : ℂ) * u‖ ^ 2) 0 ^ α = _
    rw [show 1 - ‖1 + ((-R : ℝ) : ℂ) * u‖ ^ 2 = R * (2 * u.re - R * ‖u‖ ^ 2) by
      simp [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul, Complex.mul_re]; ring,
      ← mul_zero R, ← mul_max_of_nonneg _ _ hR.le, Real.mul_rpow hR.le (le_max_right _ _)]
    rfl
  rw [measureReal_def, Measure.measure_inter_eq_of_ae (ae_mem_disk_weightedArea α),
    hμ, withDensity_apply _ Metric.isOpen_ball.measurableSet, ← integral_eq_lintegral_of_nonneg_ae (.of_forall hn)
      ((measurable_const.mul hm).aestronglyMeasurable), integral_const_mul,
    he, integral_smul_measure,
    integral_map_equiv e f,
    ENNReal.toReal_ofReal (sq_nonneg R)]
  change R ^ (-(α + 2)) * ((α + 1) * (R ^ 2 • ∫ u, f (e u) ∂diskArea)) = _
  simp_rw [eq, integral_const_mul, smul_eq_mul]
  have hRpow : R ^ (-(α + 2)) * (R ^ α * R ^ 2) = 1 := by
    rw [← Real.rpow_two R, ← Real.rpow_add hR, ← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero]
  linear_combination ((α + 1) * ∫ u, capProfile α R u ∂diskArea) * hRpow

/-- The boundary concentration lower bound uses ordinary integrable complex inputs. -/
theorem boundaryConstant_le_weightedProjection_constant (α : ℝ) (hα : 0 ≤ α) :
    ENNReal.ofReal (boundaryConstant α) ≤
      weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  rcases hα.eq_or_lt with rfl | hα
  · exact (by norm_num [boundaryConstant] : ENNReal.ofReal (boundaryConstant 0) ≤ 1).trans
      (one_le_weightedProjection_constant 0 (by norm_num))
  have hα' : -1 < α := by linarith
  let := weightedArea_isProbabilityMeasure α hα'
  apply le_sInf
  intro C hC
  have hc : Continuous (fun R ↦ ∫ z, capProfile α R z ∂diskArea) :=
    continuousOn_univ.mp (continuousOn_integral_of_compact_support (isCompact_closedBall 0 1)
      (ae_mem_disk.mono fun _ h ↦ Metric.ball_subset_closedBall h) (continuous_capProfile hα.le).continuousOn)
  have hlim := (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))) |>.const_mul (α + 1)
  rw [integral_halfDiskPower hα, show (α + 1) * (gammaConstant α / (α + 2)) = boundaryConstant α by
    unfold boundaryConstant; ring] at hlim
  apply le_of_tendsto (ENNReal.tendsto_ofReal hlim)
  filter_upwards [self_mem_nhdsWithin] with R (hR : 0 < R)
  rw [← weightedArea_boundaryCap_rescaled hα hR, ENNReal.ofReal_mul (by positivity), measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  refine column_le_weakBound hα' hC (a := 1) (by simp [disk, closure_ball])
    (measurableSet_disk.inter Metric.isOpen_ball.measurableSet) inter_subset_left ?_ (Real.rpow_pos_of_pos hR _)
  intro z hz
  have h := hz.2
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at h
  simp only [norm_weightedKernel, star_one, mul_one]
  exact Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr (by
    simpa using kernel_denominator_ne_zero (w := 1) hz.1 (by simp))) h.le (by linarith)

end BergmanWeakType
