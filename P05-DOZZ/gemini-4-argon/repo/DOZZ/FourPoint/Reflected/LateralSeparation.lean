/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.Field
import Mathlib.Tactic

/-! # Separated-region lateral covariance bounds

The plane-coordinate form of [KRV, (majkah)]. The estimate is
uniform in both angular variables and applies throughout the ξ window.
-/

public section

namespace DOZZ.Proofs



/-- Relative-radius separation gives the cross-covariance error used by Kahane. -/
theorem reflected_lateral_cross_bound_relative w v ρ
    (hw : w ≠ 0) (hv : v ≠ 0) (hρ : ρ ≤ 1 / 2) (hsep : ‖v‖ ≤ ρ * ‖w‖) :
    |gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v| ≤ 2 * ρ := by
  have reflected_lateral_cross_bound (hsep : ‖v‖ ≤ ‖w‖ / 2) : |gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v| ≤ 2 * (‖v‖ / ‖w‖) := by
    have reflected_log_near_one_bound x q (hq : 0 ≤ q) (hq₂ : q ≤ 1 / 2) (hlo : 1 - q ≤ x) (hhi : x ≤ 1 + q) : |Real.log x| ≤ 2 * q := by
      have hx : 0 < x := by linarith only [hlo, hq₂]
      rw [abs_le]
      constructor <;> linarith only [(Real.log_le_sub_one_of_pos hx), (Real.one_sub_inv_le_log_of_pos hx), (show x⁻¹ ≤ 1 + 2 * q by rw [inv_eq_one_div, div_le_iff₀ hx]; nlinarith only [(mul_le_mul_of_nonneg_left hlo (by linarith only [hq]) : (1 + 2 * q) * (1 - q) ≤ (1 + 2 * q) * x), hq, hq₂]), hhi, hq]
    have hwpos := norm_pos_iff.mpr hw
    have hnorm : ‖v‖ < ‖w‖ := by linarith only [hsep, hwpos]
    rw [origin_lateralKernel_cancellation hw hv, max_eq_left hnorm.le]
    rw [(show -Real.log ‖w - v‖ + Real.log ‖w‖ = -Real.log (‖w - v‖ / ‖w‖) by rw [Real.log_div (norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hnorm.ne (congrArg norm h.symm)))).ne' hwpos.ne']; ring), abs_neg]
    exact (reflected_log_near_one_bound (‖w - v‖ / ‖w‖) (‖v‖ / ‖w‖) (div_nonneg (norm_nonneg _) hwpos.le) ((div_le_iff₀ hwpos).mpr (by linarith only [hsep])) (by rw [← div_self hwpos.ne', ← sub_div, div_le_div_iff_of_pos_right hwpos]; linarith only [(by simpa only [sub_add_cancel] using norm_add_le (w - v) v)]) (by rw [← div_self hwpos.ne', ← add_div, div_le_div_iff_of_pos_right hwpos]; exact (norm_sub_le w v)))
  have hwpos := norm_pos_iff.mpr hw
  have hhalf : ‖v‖ ≤ ‖w‖ / 2 := by
    calc
      ‖v‖ ≤ ρ * ‖w‖ := hsep
      _ ≤ (1 / 2) * ‖w‖ := mul_le_mul_of_nonneg_right hρ hwpos.le
      _ = ‖w‖ / 2 := by ring
  exact (reflected_lateral_cross_bound hhalf).trans
    (mul_le_mul_of_nonneg_left ((div_le_iff₀ hwpos).mpr hsep) (by norm_num))

end DOZZ.Proofs
