/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterWickCopy

/-! First-order control of the pin-copy correction after Wick normalization. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A global exponential increment bound, valid without a smallness restriction. -/
theorem exp_sub_one_bound (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht))]
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (Real.exp_nonneg t)
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero t)] at h
    nlinarith
  · have ht' := lt_of_not_ge ht
    rw [abs_of_neg ht', abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr ht'.le))]
    have h := Real.add_one_le_exp t
    have he : 1 ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
    nlinarith

/-- Size of the random coefficient multiplying the distance from the insertion center. -/
noncomputable def pinCorrectionEnvelope (z : ℂ) (γ N Nbar : ℝ) : ℝ :=
  |γ| / (2 * Real.log ‖z‖) * |Nbar - N| + γ ^ 2

/-- The correction exponent has a uniform linear bound on the unit insertion disk. -/
theorem pin_correction_exponent_bound (z x : ℂ) (γ N Nbar : ℝ)
    (hz : 2 ≤ ‖z‖) (hx : ‖x‖ ≤ 1) :
    |γ * localPinCoefficient z x * (Nbar - N) -
      γ ^ 2 * (Real.log ‖z + x‖ - Real.log ‖z‖)| ≤
      pinCorrectionEnvelope z γ N Nbar * ‖x‖ := by
  calc
    _ ≤ |γ * localPinCoefficient z x * (Nbar - N)| +
        |γ ^ 2 * (Real.log ‖z + x‖ - Real.log ‖z‖)| := abs_sub ..
    _ = |γ| * |localPinCoefficient z x| * |Nbar - N| +
        γ ^ 2 * |Real.log ‖z + x‖ - Real.log ‖z‖| := by
      simp
    _ ≤ |γ| * (‖x‖ / (2 * Real.log ‖z‖)) * |Nbar - N| + γ ^ 2 * ‖x‖ := add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (local_pin_coefficient_bound z x hz hx) (abs_nonneg γ))
          (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (offCenter_pin_potential_bound z x hz hx) (sq_nonneg γ))
    _ = _ := by unfold pinCorrectionEnvelope; ring

end DOZZ.Proofs
