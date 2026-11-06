/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.BivariateCoefficientMatrix
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! Coefficient and determinant bounds for the integer closed-form matrix. -/

namespace CCDN
open Polynomial Matrix

/-- Every coefficient of the integer bivariate polynomial `f` has absolute value at most `H`. -/
def BivariateCoefficientBound (f : ℤ[X][X]) (H : ℝ) : Prop :=
  ∀ i j, |(((f.coeff i).coeff j : ℤ) : ℝ)| ≤ H

/-- The `k`-th coefficient of `monomial n a * f` is `a * f.coeff (k - n)` if `n ≤ k` and zero
otherwise. -/
lemma coeff_monomial_mul_at {R : Type*} [CommRing R]
    (f : R[X]) (a : R) (n k : ℕ) :
    (monomial n a * f).coeff k = if n ≤ k then a * f.coeff (k - n) else 0 := by
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp_all

/-- Multiplying an integer bivariate polynomial with coefficients bounded by `H ≥ 0` by a monomial
with coefficient `a` gives coefficients bounded by `|a| * H`. -/
lemma bivariateCoefficientBound_monomial_mul
    {f : ℤ[X][X]} {H : ℝ} (hH : 0 ≤ H) (hf : BivariateCoefficientBound f H)
    (a : ℤ) (m n : ℕ) :
    BivariateCoefficientBound (monomial m (monomial n a) * f) (|(a : ℝ)| * H) := by
  intro i j
  rw [coeff_monomial_mul_at]
  split_ifs
  · rw [coeff_monomial_mul_at]
    split_ifs
    · simp
      exact mul_le_mul_of_nonneg_left (hf _ _) (abs_nonneg _)
    · simpa using mul_nonneg (abs_nonneg (a : ℝ)) hH
  · simpa using mul_nonneg (abs_nonneg (a : ℝ)) hH

section
variable {H K : ℝ}

lemma bivariateCoefficientBound_sub {f g : ℤ[X][X]}
    (hf : BivariateCoefficientBound f H) (hg : BivariateCoefficientBound g K) :
    BivariateCoefficientBound (f - g) (H + K) := by
  intro i j
  simp
  exact (abs_sub _ _).trans (add_le_add (hf i j) (hg i j))

/-- A coefficient bound `H` for `f` implies every larger coefficient bound `K`. -/
lemma bivariateCoefficientBound_mono {f : ℤ[X][X]}
    (hf : BivariateCoefficientBound f H) (h : H ≤ K) :
    BivariateCoefficientBound f K := fun i j => (hf i j).trans h

end

section
variable {R : Type*} [CommRing R] (d : ℕ) (i : BivariateGrid d)

lemma bivariateGridPolynomial_single
    (a : R) :
    bivariateGridPolynomial R d (Pi.single i a) =
      monomial i.1.val (monomial i.2.val a) := by
  simp [bivariateGridPolynomial, Pi.single_apply, apply_ite]

/-- The standard basis vector of the first block decodes to the pair `(monomial, 0)` with the
corresponding grid monomial. -/
lemma closedFormPair_single_inl
    :
    closedFormPair R d (Pi.single (.inl i) 1) =
      (monomial i.1.val (monomial i.2.val 1), 0) := by
  apply Prod.ext
  · change bivariateGridPolynomial R d _ = _
    convert bivariateGridPolynomial_single d i (1 : R) using 1
    congr 1
    grind
  · change bivariateGridPolynomial R d _ = 0
    exact (bivariateGridPolynomial R d).map_zero

/-- The standard basis vector of the second block decodes to the pair `(0, monomial)` with the
corresponding grid monomial. -/
lemma closedFormPair_single_inr
    :
    closedFormPair R d (Pi.single (.inr i) 1) =
      (0, monomial i.1.val (monomial i.2.val 1)) := by
  apply Prod.ext
  · change bivariateGridPolynomial R d _ = 0
    exact (bivariateGridPolynomial R d).map_zero
  · change bivariateGridPolynomial R d _ = _
    convert bivariateGridPolynomial_single d i (1 : R) using 1
    congr 1
    grind

end

section
variable {f : ℤ[X][X]} {H : ℝ} (d : ℕ) (hH : 0 ≤ H) (hf : BivariateCoefficientBound f H)
include hH hf

/-- Inner differentiation costs at most the inner degree. -/
lemma bivariateCoefficientBound_innerDerivative
    (hd : ∀ i, (f.coeff i).natDegree ≤ d) :
    BivariateCoefficientBound ((bivariateCoefficientDerivative ℤ) f) (d * H) := by
  intro i j
  rw [coeff_bivariateCoefficientDerivative, coeff_derivative]
  by_cases hj : j + 1 ≤ d
  · simp [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ j + 1 by positivity)]
    rw [← Nat.cast_add_one]
    calc
      _ ≤ H * (j + 1 : ℕ) := mul_le_mul_of_nonneg_right (hf i (j + 1)) (Nat.cast_nonneg _)
      _ ≤ H * d := mul_le_mul_of_nonneg_left (mod_cast hj) hH
      _ = _ := mul_comm _ _
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hd i) (by omega))]
    simpa using mul_nonneg (Nat.cast_nonneg d) hH

/-- Outer differentiation costs at most the outer degree. -/
lemma bivariateCoefficientBound_outerDerivative
    (hd : f.natDegree ≤ d) :
    BivariateCoefficientBound f.derivative (d * H) := by
  intro i j
  rw [coeff_derivative]
  by_cases hi : i + 1 ≤ d
  · rw [show (i : ℤ[X]) + 1 = C ((i : ℤ) + 1) by simp, coeff_mul_C]
    simp [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ i + 1 by positivity)]
    rw [← Nat.cast_add_one]
    calc
      _ ≤ H * (i + 1 : ℕ) := mul_le_mul_of_nonneg_right (hf (i + 1) j) (Nat.cast_nonneg _)
      _ ≤ H * d := mul_le_mul_of_nonneg_left (mod_cast hi) hH
      _ = _ := mul_comm _ _
  · rw [coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))]
    simpa using mul_nonneg (Nat.cast_nonneg d) hH

end

