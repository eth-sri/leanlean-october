/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.PolarIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The uniform mass coordinate for weighted disk area -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace BergmanWeakType

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A radius whose exterior weighted disk has measure `y`. -/
def massRadius (α y : ℝ) : ℝ := sqrt (1 - y ^ (α + 1)⁻¹)

theorem massRadius_mem_unit {α y : ℝ} (hα : -1 < α) (hy : y ∈ Ioo (0 : ℝ) 1) :
    massRadius α y ∈ Ioo (0 : ℝ) 1 := by
  have hp : 0 < α + 1 := by linarith
  have hpow := rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hp)
  constructor
  · exact sqrt_pos.mpr (sub_pos.mpr hpow)
  · exact (sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
      (by simpa using sub_lt_self (1 : ℝ) (rpow_pos_of_pos hy.1 (α + 1)⁻¹))

theorem integral_weightedArea_eq_circleAverage_mass [CompleteSpace E] {α : ℝ}
    (hα : -1 < α) {f : ℂ → E} (hf : Integrable f (weightedArea α)) :
    ∫ z, f z ∂weightedArea α =
      ∫ y in (0 : ℝ)..1, circleAverage f 0 (massRadius α y) := by
  have hp : 0 < α + 1 := by linarith
  rw [integral_weightedArea_eq_diskArea hα,
    integral_diskArea_eq_circleAverage_sqrt_one_sub (integrable_weightedDensity_smul hα hf)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    integral_unit_interval_rpow hp (fun y ↦ circleAverage f 0 (massRadius α y))]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y hy
  have hs : 0 ≤ 1 - y := sub_nonneg.mpr hy.2.le
  have hrad : massRadius α (y ^ (α + 1)) = sqrt (1 - y) := by
    simp only [massRadius, rpow_rpow_inv hy.1.le hp.ne']
  dsimp only
  rw [hrad, add_sub_cancel_right, ← circleAverage_fun_smul]
  apply circleAverage_congr_sphere
  intro z hz
  have hn : ‖z‖ = sqrt (1 - y) := by
    simpa only [Metric.mem_sphere, dist_zero_right, abs_of_nonneg (sqrt_nonneg _)] using hz
  dsimp only
  rw [hn, sq_sqrt hs, sub_sub_cancel]

end BergmanWeakType
