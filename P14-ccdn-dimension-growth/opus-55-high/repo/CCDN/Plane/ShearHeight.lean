/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.ShearNormalization

/-! Explicit coefficient-height bounds for the bounded integral shear. -/

namespace CCDN
open Polynomial

section
variable {R : Type*} [CommRing R]

lemma bivariateShear_outerX (a : R) :
    bivariateShear R a (X : R[X][X]) = X := by
  rw [← bivariatePolynomialEquiv_X_zero, bivariateShear_equiv]
  change bivariatePolynomialEquiv R (MvPolynomial.aeval _ (MvPolynomial.X 0)) = _
  simp

lemma bivariateShear_innerX (a : R) :
    bivariateShear R a (C X : R[X][X]) = C X + C (C a) * X := by
  rw [← bivariatePolynomialEquiv_X_one, bivariateShear_equiv]
  change bivariatePolynomialEquiv R (MvPolynomial.aeval _ (MvPolynomial.X 1)) = _
  simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add, map_mul,
    bivariatePolynomialEquiv_X_one, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_C]

lemma bivariateShear_constant (a c : R) :
    bivariateShear R a (C (C c)) = C (C c) :=
  (bivariateShear R a).commutes c

lemma bivariateShear_monomial
    (a c : R) (i j : ℕ) :
    bivariateShear R a (monomial i (monomial j c)) =
      monomial i (monomial 0 c) * (C X + C (C a) * X) ^ j := by
  have he : monomial i (monomial j c) = C (C c) * X ^ i * (C X) ^ j := by
    rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
    grind
  rw [he, map_mul, map_mul, map_pow, map_pow, bivariateShear_outerX,
    bivariateShear_innerX, bivariateShear_constant]
  simp [← C_mul_X_pow_eq_monomial, pow_zero, mul_one]

end

lemma bivariateCoefficientBound_add {f g : ℤ[X][X]} {H K : ℝ}
    (hf : BivariateCoefficientBound f H) (hg : BivariateCoefficientBound g K) :
    BivariateCoefficientBound (f + g) (H + K) := by
  intro i j
  simp
  exact (abs_add_le _ _).trans (add_le_add (hf i j) (hg i j))

section
variable (a : ℤ)

lemma bivariateCoefficientBound_shear_linear_mul
    {f : ℤ[X][X]} {H : ℝ} (hH : 0 ≤ H) (hf : BivariateCoefficientBound f H) :
    BivariateCoefficientBound ((C X + C (C a) * X) * f) ((1 + |(a : ℝ)|) * H) := by
  have h₁ := bivariateCoefficientBound_monomial_mul hH hf 1 0 1
  have h₂ := bivariateCoefficientBound_monomial_mul hH hf a 1 0
  have hh := bivariateCoefficientBound_add h₁ h₂
  have he : monomial 0 (monomial 1 (1 : ℤ)) * f + monomial 1 (monomial 0 a) * f =
      (C X + C (C a) * X) * f := by
    simp [← C_mul_X_pow_eq_monomial, pow_zero, pow_one, map_one, one_mul, mul_one]
    ring
  rw [he] at hh
  convert hh using 1
  simp
  ring

lemma bivariateCoefficientBound_shear_linear_pow (n : ℕ) :
    BivariateCoefficientBound ((C X + C (C a) * X : ℤ[X][X]) ^ n)
      ((1 + |(a : ℝ)|) ^ n) := by
  induction n with
  | zero =>
    simp
    intro i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [coeff_one, hi, hj]
  | succ n ih =>
    rw [pow_succ', pow_succ']
    exact bivariateCoefficientBound_shear_linear_mul a (by positivity) ih

end

lemma bivariateCoefficientBound_sum {ι : Type*} [Fintype ι]
    (f : ι → ℤ[X][X]) (H : ℝ) (hf : ∀ i, BivariateCoefficientBound (f i) H) :
    BivariateCoefficientBound (∑ i, f i) ((Fintype.card ι : ℝ) * H) := by
  intro i j
  simp
  calc
    _ ≤ ∑ k : ι, |(((f k).coeff i).coeff j : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, H := Finset.sum_le_sum (fun k _ => hf k i j)
    _ = _ := by simp

