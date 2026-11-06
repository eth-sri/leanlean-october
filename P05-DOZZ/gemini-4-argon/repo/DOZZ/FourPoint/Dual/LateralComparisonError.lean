/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SeparatedRegions
import Mathlib.Tactic
/-! Quantitative real error from the two conditional lateral comparisons. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Two multiplicative comparisons, with one bounded expectation, give a signed real error
linear in their small Gaussian correction exponent. Both expectations are proved finite. -/
theorem dual_lateral_comparison_real_bound (a b : ℝ≥0∞) t C
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hC : 0 ≤ C) (ha : a ≤ ENNReal.ofReal C)
    (hab : a ≤ ENNReal.ofReal (Real.exp t)*b)
    (hba : b ≤ ENNReal.ofReal (Real.exp t)*a) :
    |a.toReal-b.toReal| ≤ (2*Real.exp 1*C)*t := by
  have haFin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha
  have hyx : b.toReal ≤ Real.exp t*a.toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos t).le] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top haFin) hba
  have hxC : a.toReal ≤ C := by
    simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top ha
  have hm1 := Real.one_le_exp_iff.mpr ht
  have hd0 := sub_nonneg.mpr hm1
  have hleft : a.toReal-b.toReal ≤ (Real.exp t-1)*(Real.exp t*C) := by
    calc
      a.toReal-b.toReal ≤ (Real.exp t-1)*b.toReal := by linarith only [(by simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos t).le] using ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top haFin) hba)) hab)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hyx.trans (mul_le_mul_of_nonneg_left hxC (Real.exp_pos t).le)) hd0
  have hright : b.toReal-a.toReal ≤ (Real.exp t-1)*(Real.exp t*C) := by
    calc
      b.toReal-a.toReal ≤ (Real.exp t-1)*a.toReal := by linarith only [hyx]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hxC.trans (le_mul_of_one_le_left hC hm1)) hd0
  have hbd : (Real.exp t-1)*(Real.exp t*C) ≤ (2*Real.exp 1*C)*t := by
    calc
      _ ≤ (2*t)*(Real.exp 1*C) :=
        mul_le_mul (by simpa only [abs_of_nonneg (sub_nonneg.mpr hm1), abs_of_nonneg ht] using (Real.abs_exp_sub_one_le (x := t) (by simpa only [abs_of_nonneg ht] using ht1))) (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht1) hC) (by positivity) (by positivity)
      _ = _ := by ring
  exact abs_le.mpr ⟨by linarith only [hright.trans hbd], hleft.trans hbd⟩

end DOZZ.Proofs
