/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! Coefficientwise and outer derivatives of bivariate polynomials, and their
compatibility with rational differentiation, for the closed-form criterion. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial
open scoped Polynomial.Bivariate

/-- Differentiate the inner variable of a bivariate polynomial. -/
def bivariateCoefficientDerivative (F : Type*) [CommRing F] :
    Derivation F F[X][X] F[X][X] :=
  PolynomialModule.equivPolynomialSelf.compDer Polynomial.derivative'.mapCoeffs

variable {R : Type*} [CommRing R] (m n : ℕ) (a : R) {F : Type*}

/-- The `n`-th outer coefficient of the inner derivative of `p` is the derivative of the `n`-th
outer coefficient of `p`. -/
@[simp]
lemma coeff_bivariateCoefficientDerivative [CommRing F] (p : F[X][X]) (n : ℕ) :
    ((bivariateCoefficientDerivative F) p).coeff n = (p.coeff n).derivative := rfl

/-- The inner derivative of the monomial with outer exponent `m`, inner exponent `n` and
coefficient `a` is the monomial with exponents `m`, `n - 1` and coefficient `a * n`. -/
lemma bivariateCoefficientDerivative_monomial :
    (bivariateCoefficientDerivative R) (monomial m (monomial n a)) =
      monomial m (monomial (n - 1) (a * n)) := by
  ext i
  simp only [coeff_bivariateCoefficientDerivative, coeff_monomial]
  split_ifs <;> simp [derivative_monomial]

/-- Differentiate a bivariate monomial in the outer variable. -/
lemma bivariate_derivative_monomial :
    (monomial m (monomial n a)).derivative = monomial (m - 1) (monomial n (a * m)) := by
  rw [derivative_monomial, ← map_natCast C m, monomial_mul_C]

end
end CCDN
