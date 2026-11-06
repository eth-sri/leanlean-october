/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Weighted.Normalizer
import BergmanWeakType.Rigidity.PolarIntegral
import Mathlib.Tactic

variable {α : ℝ}

/-! # The half-disk power integral in the boundary concentration limit -/



noncomputable section

open MeasureTheory Set Real


namespace BergmanWeakType

/-- The limiting density after blowing up a boundary cap at the point one. -/
def halfDiskPower (α : ℝ) (z : ℂ) : ℝ :=
  max (2 * z.re) 0 ^ α

variable (hα : 0 < α)
include hα

theorem continuous_halfDiskPower : Continuous (halfDiskPower α) := by
  unfold halfDiskPower
  fun_prop (disch := positivity)

theorem integral_halfDiskPower : ∫ z, halfDiskPower α z ∂diskArea = gammaConstant α / (α + 2) :=
  by
  rw [integral_diskArea_eq_circleAverage (((continuous_halfDiskPower hα).continuousOn.integrableOn_compact
    (isCompact_closedBall 0 1) (μ := area)).mono_set Metric.ball_subset_closedBall)]
  have heq :
    ∫ r in unitIoo, (2 * r) • circleAverage (halfDiskPower α) 0 r = gammaConstant α * ∫ r in unitIoo, r ^ (α + 1) :=
    by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    have hr0 := hr.1
    let H := fun θ ↦ halfDiskPower α (circleMap 0 r (θ + -(π / 2)))
    have hHc : Continuous H := (continuous_halfDiskPower hα).comp (by fun_prop)
    have hpoint (θ) : H θ = if 0 < sin θ then (2 * r) ^ α * sin θ ^ α else 0 :=
      by
      dsimp [H, halfDiskPower]
      rw [circleMap_zero_re, ← sub_eq_add_neg, cos_sub_pi_div_two]
      split_ifs with hs
      · rw [max_eq_left (by positivity)]
        rpow_ring
      · rw [max_eq_right (by nlinarith), Real.zero_rpow hα.ne']
    have hleft : ∫ θ in 0..π, H θ = (2 * r) ^ α * ∫ θ in 0..π, sin θ ^ α :=
      by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le pi_pos.le
      intro θ hθ
      rw [hpoint, ite_eq_left (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)]
    have hright : ∫ θ in π..2 * π, H θ = 0 :=
      by
      rw [← intervalIntegral.integral_zero]
      apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [pi_pos])
      intro θ hθ
      have := sin_nonpos_of_nonpos_of_neg_pi_le
        (show θ - 2 * π ≤ 0 by grind) (by grind)
      simp_all
    rw [circleAverage_eq_integral_add _]
    simp only [smul_eq_mul]
    rw [←
      intervalIntegral.integral_add_adjacent_intervals (hHc.intervalIntegrable 0 π) (hHc.intervalIntegrable π _),
      hleft, hright, add_zero, integral_sin_rpow (by linarith), Real.mul_rpow zero_le_two hr.1.le, Real.rpow_add hr.1, Real.rpow_one]
    field
  rw [heq, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by linarith))]
  rw [one_rpow, zero_rpow (by linarith), sub_zero]
  ring

end BergmanWeakType
