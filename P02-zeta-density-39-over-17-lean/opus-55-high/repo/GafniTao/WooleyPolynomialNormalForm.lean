module
public import GafniTao.WooleyEquation717Tuple
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.Support

@[expose] public section

/-!
# Finite-degree normal form for Wooley polynomial systems

Wooley Sections 4 and 7 split each polynomial into its coefficients through
degree `k` and a tail divisible by `t^(k+1)`.  This file makes that split
canonical using monic polynomial division.  It is the first exact step toward
the integral linear changes of equations used before (4.6) and (7.7).
-/

open Finset Polynomial

namespace GafniTao

noncomputable section

/-- Remainder after division by `X^d`: the coefficients below degree `d`. -/
def wooleyPolynomialLowPart (d : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  f %ₘ (X ^ d)

/-- Quotient after division by `X^d`: the exact high-degree tail. -/
def wooleyPolynomialTail (d : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  f /ₘ (X ^ d)

theorem wooleyPolynomial_low_add_tail
    (d : ℕ) (f : Polynomial ℤ) :
    wooleyPolynomialLowPart d f +
        X ^ d * wooleyPolynomialTail d f = f := by
  exact modByMonic_add_div f (X ^ d)

/-- Division by `X^d` does not alter a coefficient below degree `d`. -/
theorem wooleyPolynomialLowPart_coeff
    {d n : ℕ} (hn : n < d) (f : Polynomial ℤ) :
    (wooleyPolynomialLowPart d f).coeff n = f.coeff n := by
  have h := congrArg (fun g : Polynomial ℤ => g.coeff n)
    (wooleyPolynomial_low_add_tail d f)
  simpa only [coeff_add, coeff_X_pow_mul', ite_eq_right (not_le.mpr hn), add_zero]
    using h

/-- The `k×k` matrix of coefficients of `X,...,X^k` in the canonical low
part.  Rows are degrees and columns are source equations. -/
def wooleyPolynomialSystemLowMatrix {k : ℕ}
    (phi : WooleyPolynomialSystem k) : Matrix (Fin k) (Fin k) ℤ :=
  fun i j => (wooleyPolynomialLowPart (k + 1) (phi j)).coeff ((i : ℕ) + 1)

end

end GafniTao
