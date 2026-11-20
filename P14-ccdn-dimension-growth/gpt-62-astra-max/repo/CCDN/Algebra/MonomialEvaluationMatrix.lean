/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Height.Box
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Evaluation matrices and auxiliary polynomials

A coefficient vector in the kernel of the monomial evaluation matrix produces a polynomial
vanishing at every specified point. Injectivity of the list of monomials ensures that a
nonzero vector produces a nonzero polynomial.
-/

@[expose] public section

namespace CCDN

open Matrix

variable {n N s M : ℕ} (mon : Fin N → (Fin n →₀ ℕ)) (points : Fin s → (Fin n → ℤ))
    (hmon : Function.Injective mon) (v : Fin N → ℤ)

/-- The integer polynomial `∑ j, v j * X ^ mon j` with coefficient vector `v` on the list of
monomials `mon`. -/
noncomputable def polynomialOfCoefficients : IntegerPolynomial n :=
  ∑ j, MvPolynomial.monomial (mon j) (v j)

include hmon in
/-- For an injective list of monomials `mon`, the coefficient of `mon j` in
`polynomialOfCoefficients mon v` is `v j`. -/
theorem coefficient_polynomialOfCoefficients (j : Fin N) :
    (polynomialOfCoefficients mon v).coeff (mon j) = v j := by
  simp [polynomialOfCoefficients, MvPolynomial.coeff_monomial, hmon.eq_iff]

/-- The monomial evaluation matrix, whose entry in row `i` and column `j` is the value of the
monomial `mon j` at the integer point `points i`. -/
noncomputable def evaluationMatrix : Matrix (Fin s) (Fin N) ℤ :=
  fun i j => (mon j).prod fun k e => points i k ^ e

/-- The value of `polynomialOfCoefficients mon v` at `points i` is the `i`-th entry of the
product of the monomial evaluation matrix with `v`. -/
theorem eval_polynomialOfCoefficients (i : Fin s) :
    MvPolynomial.eval (points i) (polynomialOfCoefficients mon v) =
      (evaluationMatrix mon points *ᵥ v) i := by
  simp [polynomialOfCoefficients, evaluationMatrix, Matrix.mulVec, dotProduct,
    MvPolynomial.eval_monomial, mul_comm]

/-- If the integer point `x` lies in the box of radius `B ≥ 1` and the exponent `e` has degree
at most `M`, then the monomial `x ^ e` has absolute value at most `B ^ M`. -/
theorem abs_monomial_value_le (e : Fin n →₀ ℕ) (x : Fin n → ℤ)
    {B : ℝ} (hB : 1 ≤ B) (hx : InBox x B)
    (he : e.degree ≤ M) :
    |((e.prod (fun i k => x i ^ k) : ℤ) : ℝ)| ≤ B ^ M := by
  have hsum := by rwa [Finsupp.degree_eq_sum] at he
  rw [Finsupp.prod_fintype e (fun i k => x i ^ k) (fun _ => pow_zero _)]
  push_cast
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ i : Fin n, B ^ e i := by
      apply Finset.prod_le_prod₀
      simp
      grind [pow_le_pow_left₀]
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ B ^ M := pow_le_pow_right₀ hB hsum

end CCDN
