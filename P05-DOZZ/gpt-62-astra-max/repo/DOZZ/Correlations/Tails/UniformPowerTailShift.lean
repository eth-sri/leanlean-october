/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ShiftedPowerBound

/-! Uniform control of the leading tail at the shifted thresholds in the localization sandwich. -/

@[expose] public section
open Set

namespace DOZZ.Proofs

theorem uniform_power_tail_shift
    (T : ℝ → ℝ) (x y p P η a c cmax E : ℝ)
    (hx : 1 ≤ x) (hy : y ∈ Icc (1/2 : ℝ) (3/2 : ℝ))
    (hp : 0 ≤ p) (hpP : p ≤ P) (hη : 0 < η) (ha : η ≤ a)
    (hc : 0 ≤ c) (hcc : c ≤ cmax) (hE : 0 ≤ E)
    (hshift : |y-1| ≤ x^(-a))
    (hTail : |T (x*y)-c*(x*y)^(-p)| ≤ E*(x*y)^(-p-η)) :
    |T (x*y)-c*x^(-p)| ≤
      (E*2^(P+η)+cmax*P*2^(P+1))*x^(-p-η) := by
  have hx0 := zero_lt_one.trans_le hx
  have hy0 : 0 < y := by linarith only [hy.1]
  have hP := hp.trans hpP
  have hpow (q : ℝ) : (x*y)^q = x^q*y^q := Real.mul_rpow hx0.le hy0.le
  have hsmall : x^(-p)*x^(-a) ≤ x^(-p-η) := by
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [ha])
  have hybound : y^(-p-η) ≤ 2^(P+η) := by
    calc _ ≤ (1/2 : ℝ)^(-p-η) := Real.rpow_le_rpow_of_nonpos
          (by norm_num) hy.1 (by linarith)
      _ = 2^(p+η) := by
          rw [one_div,Real.inv_rpow zero_le_two,← Real.rpow_neg zero_le_two]
          ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (add_le_add hpP le_rfl)
  have hLeading : E*(x*y)^(-p-η) ≤ (E*2^(P+η))*x^(-p-η) := by
    rw [hpow]
    have h := mul_le_mul_of_nonneg_left hybound (mul_nonneg hE (Real.rpow_nonneg hx0.le (-p-η)))
    simpa only [mul_assoc,mul_comm,mul_left_comm] using h
  have hDifference : |c*(x*y)^(-p)-c*x^(-p)| ≤
      (cmax*P*2^(P+1))*x^(-p-η) := by
    have h0 : 0 ≤ c*x^(-p) := mul_nonneg hc (Real.rpow_nonneg hx0.le _)
    have heq : c*(x*y)^(-p)-c*x^(-p) = (c*x^(-p))*(y^(-p)-1) := by
      rw [hpow]
      ring
    rw [heq,abs_mul,abs_of_nonneg h0]
    calc _ ≤ (c*x^(-p))*(P*2^(P+1)*|y-1|) :=
          mul_le_mul_of_nonneg_left (shifted_negative_power_bound p P y hp hpP hy) h0
      _ ≤ (cmax*P*2^(P+1))*(x^(-p)*x^(-a)) := by
          calc _ ≤ (c*x^(-p))*(P*2^(P+1)*x^(-a)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hshift
                    (mul_nonneg hP (Real.rpow_nonneg zero_le_two _))) h0
            _ = c*(P*2^(P+1)*(x^(-p)*x^(-a))) := by ring
            _ ≤ cmax*(P*2^(P+1)*(x^(-p)*x^(-a))) :=
                mul_le_mul_of_nonneg_right hcc (by positivity)
            _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall
          (mul_nonneg (mul_nonneg (hc.trans hcc) hP) (Real.rpow_nonneg zero_le_two _))
  grind


end DOZZ.Proofs
