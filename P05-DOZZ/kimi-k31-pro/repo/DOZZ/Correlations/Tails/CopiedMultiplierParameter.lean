/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Correlations.Tails.OffCenterMultiplier

/-! Parameter approximation of the copied Gaussian pin weight. -/


namespace DOZZ.Proofs

/-- A bounded exponential slope has an explicit parameter error envelope. -/
theorem exp_parameter_increment (b d a t u : ℝ)
    (ha : 0 ≤ a) (hb : |b| ≤ a) (htu : |t-u| ≤ 1) :
    |Real.exp (b*t+d) - Real.exp (b*u+d)| ≤
      a * Real.exp (a*(|t|+1)+|d|) * |t-u| := by
  have hδ : |b * (u-t)| ≤ a * |t-u| := by
    rw [abs_mul, abs_sub_comm u t]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hδa : |b * (u-t)| ≤ a :=
    hδ.trans (mul_le_of_le_one_right ha htu)
  have ht : b*t+d ≤ a*|t|+|d| := by
    have hbt : b*t ≤ a*|t| := (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg t))
    linarith [le_abs_self d]
  have hfactor : Real.exp (b*t+d) - Real.exp (b*u+d) =
      Real.exp (b*t+d) * (1-Real.exp (b*(u-t))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring_nf
  rw [hfactor, abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm 1]
  calc
    _ ≤ Real.exp (a*|t|+|d|) * (|b*(u-t)| * Real.exp |b*(u-t)|) :=
      mul_le_mul (Real.exp_le_exp.mpr ht) (exp_sub_one_bound _)
        (abs_nonneg _) (Real.exp_nonneg _)
    _ ≤ Real.exp (a*|t|+|d|) * ((a*|t-u|) * Real.exp a) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hδ (Real.exp_le_exp.mpr hδa)
        (Real.exp_nonneg _) (mul_nonneg ha (abs_nonneg _))) (Real.exp_nonneg _)
    _ = _ := by
      rw [show a*(|t|+1)+|d| = (a*|t|+|d|)+a by ring]
      simp [Real.exp_add]
      ring

end DOZZ.Proofs
