/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.ClosedFormHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The integer minor has the logarithmic height needed by the
fourth-power prime cutoff. The charge applies to primes with proved matrix
rank drop; identifying these with the geometric bad primes is a separate step. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix Real

variable (d r : ℕ)

private lemma log_factorial_le_square : Real.log (r.factorial : ℝ) ≤ (r : ℝ) ^ 2 := by
  by_cases hr : r = 0
  · simp [hr]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hh : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by exact_mod_cast Nat.factorial_le_pow r
  have hl := Real.log_le_log (by positivity) hh
  rw [Real.log_pow] at hl
  exact hl.trans (by nlinarith [Real.log_le_self hr0.le])

/-- The determinant height fits the cutoff L=27*d^4 with scaled
height 1+log(H)/d². -/
theorem closedForm_minor_log_height (hd : 1 ≤ d) (hr : r ≤ 2 * d ^ 2)
    (f : ℤ[X][X]) (H : ℝ) (hH : 1 ≤ H)
    (hf : BivariateCoefficientBound f H) (houter : f.natDegree ≤ d)
    (hinner : ∀ i, (f.coeff i).natDegree ≤ d)
    (a : Fin r → ℕ × ℕ) (c : Fin r → ClosedFormColumns d)
    (hD : ((closedFormCoefficientMatrix d f).submatrix a c).det ≠ 0) :
    Real.log |((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ)| ≤
      (27 * (d : ℝ) ^ 4) * (1 + Real.log H / (d : ℝ) ^ 2) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hr' : (r : ℝ) ≤ 2 * (d : ℝ) ^ 2 := by exact_mod_cast hr
  have hH0 : 0 < H := by linarith
  have hlog := Real.log_nonneg hH
  have hE0 : 0 < 2 * (d : ℝ) * H := by positivity
  have hl := Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hD)) (closedForm_integer_minor_bound d r f H hH0.le hf houter hinner a c)
  rw [Real.log_mul (by positivity) (pow_ne_zero _ hE0.ne'),
    Real.log_pow, Real.log_mul (by positivity) hH0.ne',
    Real.log_mul (by norm_num) hd0.ne'] at hl
  have hfac := log_factorial_le_square r
  have hl2 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)
  have hld := Real.log_le_self hd0.le
  have hd3 : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ (d : ℝ) ^ 3 by positivity) (sub_nonneg.mpr hd1)]
  have he : (27 * (d : ℝ) ^ 4) * (1 + Real.log H / (d : ℝ) ^ 2) =
      27 * (d : ℝ) ^ 4 + 27 * (d : ℝ) ^ 2 * Real.log H := by
    field_simp
  nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) hlog]

end
end CCDN
