/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.Normalizer
public import BergmanWeakType.Measure

/-! # The half-disk power integral in the boundary concentration limit -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real Metric
open scoped Topology ENNReal

namespace BergmanWeakType

/-- After rotating the cap coordinates, its height at scale zero is
`2 im u` on the upper half disk and vanishes on the lower half. -/
def capProfile (α R : ℝ) (u : ℂ) := max (2*u.im-R*‖u‖^2) 0 ^ α

theorem clip_mul {r : ℝ} (hr : 0 ≤ r) (x α : ℝ) :
    max (r*x) 0 ^ α = r^α * max x 0 ^ α := by
  rw [← mul_rpow hr (le_max_right _ _), mul_max_of_nonneg _ _ hr, mul_zero]

theorem continuous_capProfile {α : ℝ} (hα : 0 < α) : Continuous (capProfile α).uncurry := by
  unfold capProfile Function.uncurry; fun_prop (disch := positivity)

private theorem cap_average {α r : ℝ} (hα : 0 < α) (hr : 0 < r) :
    circleAverage (capProfile α 0) 0 r = r ^ α * gammaConstant α / 2 := by
  let f θ := max (sin θ) 0 ^ α
  have hf : Continuous f := by dsimp [f]; fun_prop (disch := positivity)
  have h : (∫ θ in angularInterval, f θ) = ∫ θ in 0..π, sin θ ^ α := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
      ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
    have hn : (∫ θ in -π..0, f θ) = 0 := by
      apply intervalIntegral.integral_zero_ae; filter_upwards with θ hθ
      rw [uIoc_of_le (neg_nonpos.mpr pi_pos.le)] at hθ
      simp [f,max_eq_right (sin_nonpos_of_nonpos_of_neg_pi_le hθ.2 hθ.1.le),hα.ne']
    rw [hn,zero_add]; apply intervalIntegral.integral_congr
    intro θ hθ; simp_all [f, uIcc_of_le, pi_pos.le, max_eq_left, sin_nonneg_of_nonneg_of_le_pi]
  rw [← integral_angle, angleMeasure, integral_smul_measure]
  simp only [capProfile,zero_mul,sub_zero,circleMap_zero_im,← mul_assoc,clip_mul (mul_nonneg zero_le_two hr.le),integral_const_mul]
  change _ • ((2*r)^α * ∫ θ in angularInterval, f θ) = _
  rw [h, ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_rpow zero_le_two hr.le]
  grind [pi_pos, scaled_integral_sin]

theorem integral_halfDiskPower {α : ℝ} (hα : 0 < α) :
    (∫ z, capProfile α 0 z ∂diskArea) = gammaConstant α / (α + 2) := by
  have hc : Continuous (capProfile α 0) := by unfold capProfile; fun_prop (disch := positivity)
  rw [disk_polar ((hc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall),
    integral_radialLaw (by norm_num), ← unit_integral]
  have eq : (∫ r in 0..1, radialDensity 0 r • circleAverage (capProfile α 0) 0 r) =
      gammaConstant α * ∫ r in 0..1, r ^ (α+1) := by
    rw [← intervalIntegral.integral_const_mul]; apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro r hr; simp [radialDensity,cap_average hα hr.1,rpow_add hr.1]; ring
  rw [eq,integral_rpow (by grind),one_rpow,zero_rpow (by positivity)]
  grind

end BergmanWeakType
