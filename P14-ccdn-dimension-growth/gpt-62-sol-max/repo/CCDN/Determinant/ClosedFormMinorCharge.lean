/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.ClosedFormHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CCDN.ForMathlib.Log

/-! The integer minor has the logarithmic height needed by the
fourth-power prime cutoff. The charge applies to primes with proved matrix
rank drop; identifying these with the geometric bad primes is a separate step. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix Real

/-- The determinant height fits the cutoff L=27*d^4 with scaled
height 1+log(H)/d². -/
theorem closedForm_minor_log_height
    (d r : ℕ) (hd : 1 ≤ d) (hr : r ≤ 2 * d ^ 2)
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
  have hl := Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hD))
    (closedForm_integer_minor_bound d r f H hH0.le hf houter hinner a c)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by positivity) hH0.ne', Real.log_mul (by norm_num) hd0.ne'] at hl
  have hfct := (log_factorial_le_mul_log (s := r) le_rfl).trans
    (mul_le_mul_of_nonneg_left (log_le_self (Nat.cast_nonneg r)) (Nat.cast_nonneg r))
  
  have hd3 := pow_le_pow_right₀ hd1 (show 3 ≤ 4 by decide)
  have hlog := log_nonneg hH
  calc
    _ ≤ (r : ℝ) ^ 2 + r * (2 + d + log H) := by
      nlinarith [log_le_self hd0.le, log_le_self (show (0 : ℝ) ≤ 2 by norm_num),
        mul_le_mul_of_nonneg_left (log_le_self hd0.le) (Nat.cast_nonneg r),
        mul_le_mul_of_nonneg_left (log_le_self (show (0 : ℝ) ≤ 2 by norm_num)) (Nat.cast_nonneg r)]
    _ ≤ (2 * (d : ℝ) ^ 2) ^ 2 + 2 * (d : ℝ) ^ 2 * (2 + d + log H) := by gcongr
    _ ≤ _ := by
      rw [show 27 * (d : ℝ) ^ 4 * (1 + log H / (d : ℝ) ^ 2) =
        27 * (d : ℝ) ^ 4 + 27 * (d : ℝ) ^ 2 * log H by field_simp]
      nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) hlog]

end
end CCDN
