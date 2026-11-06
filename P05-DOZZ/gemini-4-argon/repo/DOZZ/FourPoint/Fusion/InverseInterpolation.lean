/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.TimeIntegrability
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-! # Signed interpolation of positive inverse masses -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- Fundamental theorem of calculus for an inverse power along the positive mass segment. -/
theorem fusion_inverse_interpolation a b p (ha : 0 < a) (hb : 0 < b) :
    b ^ (-p) - a ^ (-p) = -p * (b - a) *
      (∫ t in Icc (0 : ℝ) 1, (t * b + (1 - t) * a) ^ (-p - 1)) := by
  let f := fun t : ℝ => t * b + (1 - t) * a
  have hfpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < f t := by
    intro t ht
    dsimp only [f]
    have := mul_nonneg ht.1 hb.le
    have := mul_nonneg (sub_nonneg.mpr ht.2) ha.le
    by_cases ht0 : t = 0
    · subst t; simpa using ha
    · have h : 0 < t * b := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hb
      linarith
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (show ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u => f u ^ (-p)) (-p * (b - a) * f t ^ (-p - 1)) t by intro t ht; convert (show HasDerivAt f (b - a) t by convert (hasDerivAt_id t).mul_const b |>.add (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const a) using 1 <;> simp [f, Pi.add_def, sub_eq_add_neg]).rpow_const (p := -p) (Or.inl (hfpos t (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)).ne') using 1; ring) (by apply ContinuousOn.intervalIntegrable; apply continuousOn_const.mul; exact (show Continuous f by dsimp only [f]; fun_prop).continuousOn.rpow_const (fun t ht => Or.inl (hfpos t (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)).ne'))
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc,
    integral_const_mul] at h
  simpa only [f, zero_mul, sub_zero, one_mul, sub_self, mul_zero, zero_add, add_zero] using h.symm
end DOZZ.Proofs
