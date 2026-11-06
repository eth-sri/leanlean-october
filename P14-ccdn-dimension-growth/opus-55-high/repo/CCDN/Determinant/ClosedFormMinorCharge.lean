/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.ClosedFormHeight
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The integer minor has the logarithmic height needed by the
fourth-power prime cutoff. The charge applies to primes with proved matrix
rank drop; identifying these with the geometric bad primes is a separate step. -/

namespace CCDN
section
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
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hr' : (r : ℝ) ≤ 2 * (d : ℝ) ^ 2 := mod_cast hr
  have hH0 : 0 < H := by linarith
  have hlog := Real.log_nonneg hH
  have hE0 : 0 < 2 * (d : ℝ) * H := by positivity
  have hb : |((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ)| ≤
      (r.factorial : ℝ) * (2 * d * H) ^ r := by
    have he : ∀ i j, |((closedFormCoefficientMatrix d f i j : ℤ) : ℝ)| ≤ 2 * d * H := by
      intro i j
      change |((((closedFormOperator f (closedFormPair ℤ d (Pi.single j 1))).coeff i.1).coeff
        i.2 : ℤ) : ℝ)| ≤ _
      have hDH := mul_nonneg (Nat.cast_nonneg d) hH0.le
      have hdi := bivariateCoefficientBound_innerDerivative d hH0.le hf hinner
      have hdo := bivariateCoefficientBound_outerDerivative d hH0.le hf houter
      cases j with
      | inl j =>
        rw [closedFormPair_single_inl]
        change |((((((bivariateCoefficientDerivative ℤ) (monomial j.1.val (monomial j.2.val 1))) * f -
          monomial j.1.val (monomial j.2.val 1) * (bivariateCoefficientDerivative ℤ) f -
          (0 : ℤ[X][X]).derivative * f + 0 * f.derivative).coeff i.1).coeff i.2 : ℤ) : ℝ)| ≤ _
        simp [map_zero, zero_mul, sub_zero, add_zero, bivariateCoefficientDerivative_monomial,
          one_mul]
        have ha := bivariateCoefficientBound_monomial_mul hH0.le hf (j.2.val : ℤ) j.1.val (j.2.val - 1)
        have hb := bivariateCoefficientBound_monomial_mul hDH hdi 1 j.1.val j.2.val
        have hh := (bivariateCoefficientBound_sub ha hb) i.1 i.2
        simp [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ j.2.val from Nat.cast_nonneg _),
          Int.cast_one, abs_one, one_mul] at hh
        have hj : (j.2.val : ℝ) ≤ d := mod_cast j.2.isLt.le
        nlinarith
      | inr j =>
        rw [closedFormPair_single_inr]
        change |(((((bivariateCoefficientDerivative ℤ) 0 * f -
          0 * (bivariateCoefficientDerivative ℤ) f -
          (monomial j.1.val (monomial j.2.val 1)).derivative * f +
          monomial j.1.val (monomial j.2.val 1) * f.derivative).coeff i.1).coeff i.2 : ℤ) : ℝ)| ≤ _
        simp [map_zero, zero_mul, sub_self, zero_sub, bivariate_derivative_monomial, one_mul]
        rw [neg_add_eq_sub]
        have ha := bivariateCoefficientBound_monomial_mul hDH hdo 1 j.1.val j.2.val
        have hb := bivariateCoefficientBound_monomial_mul hH0.le hf (j.1.val : ℤ) (j.1.val - 1) j.2.val
        have hh := (bivariateCoefficientBound_sub ha hb) i.1 i.2
        simp [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ j.1.val from Nat.cast_nonneg _),
          Int.cast_one, abs_one, one_mul] at hh
        have hj : (j.1.val : ℝ) ≤ d := mod_cast j.1.isLt.le
        nlinarith
    have hb := Matrix.det_le (abv := AbsoluteValue.abs)
      (A := ((closedFormCoefficientMatrix d f).submatrix a c).map (Int.castRingHom ℝ))
      (fun i j => he (a i) (c j))
    have hd : (((closedFormCoefficientMatrix d f).submatrix a c).map (Int.castRingHom ℝ)).det =
        ((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ) :=
      ((Int.castRingHom ℝ).map_det _).symm
    rw [hd] at hb
    simpa using hb
  have hD0 : (0 : ℝ) < |((((closedFormCoefficientMatrix d f).submatrix a c).det : ℤ) : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr hD)
  have hl := Real.log_le_log hD0 hb
  rw [Real.log_mul (by positivity : (r.factorial : ℝ) ≠ 0) (pow_ne_zero _ hE0.ne'),
    Real.log_pow, Real.log_mul (by grind) hH0.ne',
    Real.log_mul (by grind) hd0.ne'] at hl
  have hfac : Real.log (r.factorial : ℝ) ≤ (r : ℝ) ^ 2 := by
    by_cases hr : r = 0
    · simp_all
    have hr0 : (0 : ℝ) < r := by positivity
    have hh : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := mod_cast Nat.factorial_le_pow r
    have hl := Real.log_le_log (by positivity) hh
    rw [Real.log_pow] at hl
    exact hl.trans (by nlinarith [Real.log_le_self hr0.le])
  have hl2 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)
  have hld := Real.log_le_self hd0.le
  have hterm : (r : ℝ) * (Real.log 2 + Real.log d + Real.log H) ≤
      2 * (d : ℝ) ^ 2 * (2 + d + Real.log H) := by
    calc
      _ ≤ (r : ℝ) * (2 + d + Real.log H) := mul_le_mul_of_nonneg_left (by linarith) hr0
      _ ≤ _ := mul_le_mul_of_nonneg_right hr' (by positivity)
  have hrsq : (r : ℝ) ^ 2 ≤ (2 * (d : ℝ) ^ 2) ^ 2 := by nlinarith
  have hd2 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 4 := by nlinarith [sq_nonneg ((d : ℝ) ^ 2 - 1)]
  have hd3 : (d : ℝ) ^ 3 ≤ (d : ℝ) ^ 4 := by
    nlinarith
  have he : (27 * d ^ 4) * (1 + Real.log H / d ^ 2) =
      27 * (d : ℝ) ^ 4 + 27 * (d : ℝ) ^ 2 * Real.log H := by
    field_simp
  rw [he]
  nlinarith

