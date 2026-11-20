/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.RationalDifferential
public import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! Coefficientwise and outer derivatives of bivariate polynomials, and their
compatibility with rational differentiation, for the closed-form criterion. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Differential
open scoped Polynomial.Bivariate
attribute [local instance] rationalDifferential

/-- Differentiate the inner variable of a bivariate polynomial. -/
def bivariateCoefficientDerivative (F : Type*) [CommRing F] :
    Derivation F F[X][X] F[X][X] :=
  PolynomialModule.equivPolynomialSelf.compDer Polynomial.derivative'.mapCoeffs

/-- The `n`-th outer coefficient of the inner derivative of `p` is the derivative of the `n`-th
outer coefficient of `p`. -/
@[simp]
lemma coeff_bivariateCoefficientDerivative {F : Type*} [CommRing F] (p : F[X][X]) (n : ℕ) :
    ((bivariateCoefficientDerivative F) p).coeff n = (p.coeff n).derivative := rfl

section

variable {R : Type*} [CommRing R] (m n : ℕ) (a : R)
include R m n a

/-- The inner derivative of the monomial with outer exponent `m`, inner exponent `n` and
coefficient `a` is the monomial with exponents `m`, `n - 1` and coefficient `a * n`. -/
lemma bivariateCoefficientDerivative_monomial :
    (bivariateCoefficientDerivative R) (monomial m (monomial n a)) =
      monomial m (monomial (n - 1) (a * n)) := by
  ext i
  simp only [coeff_bivariateCoefficientDerivative, coeff_monomial]
  split_ifs <;> simp [derivative_monomial]

end

/-- Mapping the inner coefficients of `p` into `RatFunc F` intertwines the inner derivative with
coefficientwise rational differentiation. -/
lemma bivariateCoefficientDerivative_map {F : Type*} [Field F] (p : F[X][X]) :
    ((bivariateCoefficientDerivative F) p).map (algebraMap F[X] (RatFunc F)) =
      Differential.mapCoeffs (p.map (algebraMap F[X] (RatFunc F))) := by
  aesop

end
end CCDN
