/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionGuardDisks

/-! Deterministic kernel comparisons uniform on bounded charge intervals. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Two-sided distance comparison controls a power of either sign by a uniform factor. -/
theorem rpow_distance_comparison (x r m p L : ℝ)
    (hr : 0 < r) (hm : 1 ≤ m) (hl : r / m ≤ x) (hu : x ≤ m * r)
    (hpl : -L ≤ p) (hpu : p ≤ L) : x ^ p ≤ m ^ L * r ^ p := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hx : 0 < x := (div_pos hr hmpos).trans_le hl
  by_cases hp : 0 ≤ p
  · calc
      x ^ p ≤ (m * r) ^ p := Real.rpow_le_rpow hx.le hu hp
      _ = m ^ p * r ^ p := Real.mul_rpow hmpos.le hr.le
      _ ≤ m ^ L * r ^ p := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hm hpu) (Real.rpow_pos_of_pos hr _).le
  · calc
      x ^ p ≤ (r / m) ^ p := Real.rpow_le_rpow_of_nonpos (div_pos hr hmpos) hl (le_of_not_ge hp)
      _ = m ^ (-p) * r ^ p := by
        rw [Real.div_rpow hr.le hmpos.le, Real.rpow_neg hmpos.le, div_eq_mul_inv, mul_comm]
      _ ≤ m ^ L * r ^ p := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hm (by linarith only [hpl]))
        (Real.rpow_pos_of_pos hr _).le

end DOZZ.Proofs
