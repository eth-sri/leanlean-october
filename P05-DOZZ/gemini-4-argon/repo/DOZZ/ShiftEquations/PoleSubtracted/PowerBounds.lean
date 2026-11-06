/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Power bounds for the pole-subtracted observable

Elementary estimates that control the powers occurring in the pole-subtracted observable:

* `rpow_le_add_of_mem_Icc`: for `t ∈ [L, B]` with `0 < L`, `t ^ s ≤ B ^ s + L ^ s` for every real
  exponent `s` (the power is monotone for `s ≥ 0` and antitone for `s ≤ 0`);
* `exp_mul_le_add_of_mem_Icc`: for `a ∈ [a₁, a₂]`, `exp (a u) ≤ exp (a₁ u) + exp (a₂ u)`;
* `norm_ofReal_cpow_sub_ofReal_cpow_le`: for `0 < L ≤ B` and `w : ℂ`, the mean value inequality
  `‖B ^ w - L ^ w‖ ≤ ‖w‖ (B - L) (B ^ (Re w - 1) + L ^ (Re w - 1))`;
* `abs_rpow_sub_rpow_le`: the same bound for a real exponent.
-/

@[expose] public section

open Set

namespace DOZZ.Proofs


/-- `exp (a u)` on `[a₁, a₂]` is bounded by its endpoint values. -/
theorem exp_mul_le_add_of_mem_Icc {a a₁ a₂} (ha : a ∈ Icc a₁ a₂) u :
    Real.exp (a * u) ≤ Real.exp (a₁ * u) + Real.exp (a₂ * u) := by
  have : 0 < Real.exp (a₁ * u) := Real.exp_pos _
  have : 0 < Real.exp (a₂ * u) := Real.exp_pos _
  rcases le_total 0 u with hu | hu
  · have h := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ha.2 hu)
    linarith
  · have h := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right ha.1 hu)
    linarith


/-- **Complex powers of two positive reals** differ by at most `‖w‖ (B - L)` times the sum of
the endpoint values of `t ^ (Re w - 1)`. -/
theorem norm_ofReal_cpow_sub_ofReal_cpow_le {L B : ℝ} (hL : 0 < L) (hLB : L ≤ B) (w : ℂ) :
    ‖(B : ℂ) ^ w - (L : ℂ) ^ w‖ ≤ ‖w‖ * (B - L) * (B ^ (w.re - 1) + L ^ (w.re - 1)) := by
  have norm_mul_ofReal_cpow_sub_one_le {B : ℝ} {t : ℝ} (ht : t ∈ Icc L B) (w : ℂ) : ‖w * (t : ℂ) ^ (w - 1)‖ ≤ ‖w‖ * (B ^ (w.re - 1) + L ^ (w.re - 1)) := by
    have rpow_le_add_of_mem_Icc (s : ℝ) : t ^ s ≤ B ^ s + L ^ s := by
      have := Real.rpow_pos_of_pos (hL.trans_le (ht.1.trans ht.2)) s
      have := Real.rpow_pos_of_pos hL s
      rcases le_total 0 s with hs | hs
      · have h := Real.rpow_le_rpow (hL.le.trans ht.1) ht.2 hs
        linarith
      · have h := Real.rpow_le_rpow_of_nonpos hL ht.1 hs
        linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hL.trans_le ht.1), Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left (rpow_le_add_of_mem_Icc _) (norm_nonneg w)
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  calc ‖(B : ℂ) ^ w - (L : ℂ) ^ w‖
      ≤ ‖w‖ * (B ^ (w.re - 1) + L ^ (w.re - 1)) * (B - L) := (norm_image_sub_le_of_norm_deriv_le_segment' (fun t ht => (hasDerivAt_ofReal_cpow_const (hL.trans_le ht.1).ne' hw).hasDerivWithinAt) (fun t ht => norm_mul_ofReal_cpow_sub_one_le (Ico_subset_Icc_self ht) w) B ⟨hLB, le_rfl⟩)
    _ = ‖w‖ * (B - L) * (B ^ (w.re - 1) + L ^ (w.re - 1)) := by ring

end DOZZ.Proofs

end
