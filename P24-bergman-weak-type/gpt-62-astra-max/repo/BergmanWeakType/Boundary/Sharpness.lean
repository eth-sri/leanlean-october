/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Boundary.Concentration
public import BergmanWeakType.Boundary.HalfDiskIntegral
public import BergmanWeakType.Affine
public import Mathlib.MeasureTheory.Group.Integral

/-! # The explicit boundary lower bound for the complex weighted projection -/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Metric Filter
open scoped ENNReal Topology

namespace BergmanWeakType

/-- Test the column at `1` on a ball of radius `R` and use `z = 1+i R u`
to pull it back to the unit disk. Clipping the density at zero absorbs the
original disk cutoff, since the exponent is strictly positive. -/
private theorem cap_test {α R : ℝ} (hα : 0 < α) (hR : 0 < R) :
    ENNReal.ofReal ((α+1) * ∫ u, capProfile α R u ∂diskArea) ≤
      weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  have ha : -1 < α := by linarith
  let := weightedArea_isProbabilityMeasure α ha
  let E := disk ∩ ball 1 R
  have m : MeasurableSet E := measurableSet_disk.inter isOpen_ball.measurableSet
  have H := column_test ha (a := 1) (by simp) m inter_subset_left (L := R^(-(α+2))) ?col (by positivity)
  case col =>
    intro z hz; simp
    apply rpow_le_rpow_of_nonpos _ _ (by linarith)
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun h ↦ by simpa [← h] using (mem_disk_iff z).mp hz.1))
    · simpa [dist_eq_norm, norm_sub_rev] using (mem_ball.mp hz.2).le
  rw [← ENNReal.ofReal_toReal (measure_ne_top (weightedArea α) E), ← ENNReal.ofReal_mul (by positivity)] at H
  convert H using 2
  have mass : (weightedArea α).real E = ∫ z in ball 1 R, (α+1)*max (1-‖z‖^2) 0 ^ α ∂area := by
    rw [measureReal_def, weightedArea, withDensity_apply _ m, diskArea,
      Measure.restrict_restrict_of_subset (s := E) inter_subset_left, ← setLIntegral_indicator measurableSet_disk,
      integral_eq_lintegral_of_nonneg_ae (.of_forall fun _ ↦ by positivity) (by fun_prop (disch := positivity))]
    congr 1; apply lintegral_congr; intro z
    by_cases hz : z ∈ disk
    · have h := (mem_disk_iff z).mp hz
      simp [hz,max_eq_left (show 0 ≤ 1-‖z‖^2 by nlinarith [norm_nonneg z])]
    · have h : 1 ≤ ‖z‖ := by simp_all
      simp [hz,max_eq_right (show 1-‖z‖^2 ≤ 0 by nlinarith),hα.ne']
  have hb : (R : ℂ)*Complex.I ≠ 0 := by simp [hR.ne']
  let e := affineMeasurableEquiv 1 _ hb
  have ball := ball_area (a := 1) hb
  simp [abs_of_pos hR] at ball
  have ht (u : ℂ) : 1-‖e u‖^2 = R*(2*u.im-R*‖u‖^2) := by
    simp [e,affineMeasurableEquiv,Complex.sq_norm,Complex.normSq_apply]; ring
  change _ = R ^ (-(α+2)) * (weightedArea α).real E
  rw [mass,ball,integral_smul_measure, integral_map_equiv]
  simp_rw [show affineMeasurableEquiv 1 _ hb = e by rfl, ht, clip_mul hR.le, ← mul_assoc (α+1), integral_const_mul]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul, rpow_neg hR.le, rpow_add hR, rpow_ofNat]
  unfold capProfile; field_simp

/-- The boundary concentration lower bound uses ordinary integrable complex inputs. -/
theorem boundaryConstant_le_weightedProjection_constant (α : ℝ) (hα : 0 ≤ α) :
    ENNReal.ofReal (boundaryConstant α) ≤
      weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  rcases hα.eq_or_lt with rfl | hα
  · apply le_trans _ (one_le_weightedProjection_constant 0 (by norm_num)); norm_num [boundaryConstant]
  have h := Weighted.continuousOn_average (S := Set.univ) (isCompact_closedBall 0 1)
    (ae_mem_disk.mono fun _ hw ↦ ball_subset_closedBall hw) (continuous_capProfile hα).continuousOn
  have lim := (continuousOn_univ.mp h).continuousAt (x := 0) |>.const_mul (α+1)
  rw [show boundaryConstant α = (α+1)*(∫ u, capProfile α 0 u ∂diskArea) by grind [boundaryConstant, integral_halfDiskPower]]
  apply le_of_tendsto (x := 𝓝[>] 0) (ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt lim.continuousWithinAt)
  filter_upwards [self_mem_nhdsWithin] with R hR using cap_test hα hR

end BergmanWeakType
