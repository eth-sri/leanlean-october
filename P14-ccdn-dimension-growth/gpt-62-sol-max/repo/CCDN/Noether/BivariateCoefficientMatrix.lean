/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateClosedForms

/-! Integer coefficient matrices for the closed-form irreducibility criterion.
Columns encode pairs of polynomials in a finite rectangular monomial grid.
Rows are coefficient positions; finite independent rows will be selected when
extracting a determinant witness. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

/-- Index set of the bivariate monomials whose outer and inner exponents are both less than `d`. -/
abbrev BivariateGrid (d : ℕ) := Fin d × Fin d
/-- Index set of the unknown coefficients of a pair of polynomials supported in the grid
`BivariateGrid d`; these index the columns of the closed-form coefficient matrix. -/
abbrev ClosedFormColumns (d : ℕ) := BivariateGrid d ⊕ BivariateGrid d

/-- Reconstruct a polynomial with outer and inner exponents less than d. -/
def bivariateGridPolynomial (R : Type*) [CommRing R] (d : ℕ) :
    (BivariateGrid d → R) →ₗ[R] R[X][X] where
  toFun v := ∑ i, monomial i.1.val (monomial i.2.val (v i))
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.smul_sum]
    simp [smul_monomial]

section

variable {R : Type*} [CommRing R]
include R

/-- The coefficient with outer exponent `i` and inner exponent `j` of the polynomial with grid
coefficients `v` is `v (i, j)`. -/
lemma bivariateGridPolynomial_coeff {d : ℕ}
    (v : BivariateGrid d → R) (i j : Fin d) :
    ((bivariateGridPolynomial R d v).coeff i.val).coeff j.val = v (i,j) := by
  classical
  simp [bivariateGridPolynomial, coeff_monomial, Fintype.sum_prod_type, Fin.val_inj]

private lemma bivariateGridPolynomial_injective (d : ℕ) :
    Function.Injective (bivariateGridPolynomial R d) := by
  intro v w h
  funext i
  have hh := congrArg (fun p : R[X][X] => (p.coeff i.1.val).coeff i.2.val) h
  simpa [bivariateGridPolynomial_coeff] using hh

/-- The polynomial with coefficients `v` on the grid `BivariateGrid d` has outer degree less than
`d`. -/
lemma bivariateGridPolynomial_degree_lt {d : ℕ}
    (v : BivariateGrid d → R) : (bivariateGridPolynomial R d v).degree < d := by
  classical
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  simp only [bivariateGridPolynomial, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  rw [coeff_monomial, ite_eq_right]
  omega

end

/-- Decode the two blocks of the unknown coefficient vector. -/
def closedFormPair (R : Type*) [CommRing R] (d : ℕ) :
    (ClosedFormColumns d → R) →ₗ[R] R[X][X] × R[X][X] where
  toFun v := (bivariateGridPolynomial R d (fun i => v (.inl i)),
    bivariateGridPolynomial R d (fun i => v (.inr i)))
  map_add' v w := by
    apply Prod.ext
    · exact (bivariateGridPolynomial R d).map_add _ _
    · exact (bivariateGridPolynomial R d).map_add _ _
  map_smul' a v := by
    apply Prod.ext
    · exact (bivariateGridPolynomial R d).map_smul a _
    · exact (bivariateGridPolynomial R d).map_smul a _

/-- Decoding a coefficient vector into a pair of grid polynomials is injective. -/
lemma closedFormPair_injective {R : Type*} [CommRing R] (d : ℕ) :
    Function.Injective (closedFormPair R d) := by
  intro v w h
  have hl := bivariateGridPolynomial_injective d (congrArg Prod.fst h)
  have hr := bivariateGridPolynomial_injective d (congrArg Prod.snd h)
  funext i
  cases i with
  | inl i => exact congrFun hl i
  | inr i => exact congrFun hr i

/-- The cleared differential equation as a linear operator on (P,Q). -/
def closedFormOperator {R : Type*} [CommRing R] (f : R[X][X]) :
    (R[X][X] × R[X][X]) →ₗ[R] R[X][X] where
  toFun u := (bivariateCoefficientDerivative R) u.1 * f -
    u.1 * (bivariateCoefficientDerivative R) f - u.2.derivative * f + u.2 * f.derivative
  map_add' u v := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_mul]
    ring
  map_smul' a u := by
    simp_all [smul_sub]

/-- All polynomial coefficients as a linear map. -/
def bivariateCoefficients (R : Type*) [CommRing R] : R[X][X] →ₗ[R] (ℕ × ℕ → R) where
  toFun f := fun i => (f.coeff i.1).coeff i.2
  map_add' f g := by ext; simp
  map_smul' a f := by ext; simp

/-- A bivariate polynomial is determined by its coefficients. -/
lemma bivariateCoefficients_injective {R : Type*} [CommRing R] :
    Function.Injective (bivariateCoefficients R) := by
  intro f g h
  ext i j
  exact congrFun h (i,j)

/-- The matrix of the closed-form equation on bounded unknowns.
In particular it is an integer matrix when R=Z. -/
def closedFormCoefficientMatrix {R : Type*} [CommRing R] (d : ℕ) (f : R[X][X]) :
    Matrix (ℕ × ℕ) (ClosedFormColumns d) R :=
  LinearMap.toMatrix'
    ((bivariateCoefficients R).comp ((closedFormOperator f).comp (closedFormPair R d)))

section

variable {R : Type*} [CommRing R]

private lemma coeff_monomial_mul_at (f : R[X]) (a : R) (n k : ℕ) :
    (monomial n a * f).coeff k = if n ≤ k then a * f.coeff (k - n) else 0 := by
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp_all

/-- The two terms in the monomial Wronskian use the same shifted coefficient. -/
private lemma coeff_monomial_wronskian (f : R[X]) (a : R) (n k : ℕ) :
    ((monomial n a).derivative * f - monomial n a * f.derivative).coeff k =
      if n ≤ k + 1 then a * ((n : R) - (k + 1 - n : ℕ)) * f.coeff (k + 1 - n) else 0 := by
  rw [coeff_sub, derivative_monomial, coeff_monomial_mul_at, coeff_monomial_mul_at]
  by_cases hn : n = 0
  · subst n
    simp [coeff_derivative]
    ring
  by_cases hk : n ≤ k
  · rw [ite_eq_left (by omega), ite_eq_left hk, ite_eq_left (by omega), coeff_derivative,
      show k - (n - 1) = k + 1 - n by omega,
      ← Nat.cast_succ]
    simp only [Nat.succ_eq_add_one, show k - n + 1 = k + 1 - n by omega]
    ring
  by_cases he : n = k + 1
  · subst n
    simp [show ¬ k + 1 ≤ k by omega]
  · rw [ite_eq_right (by omega), ite_eq_right hk, ite_eq_right (by omega), sub_zero]

private lemma closedFormPair_single_inl {d : ℕ} (j : BivariateGrid d) :
    closedFormPair R d (Pi.single (.inl j) 1) =
      (monomial j.1.val (monomial j.2.val 1), 0) := by
  classical
  simp [closedFormPair, bivariateGridPolynomial, Pi.single_apply, apply_ite]

private lemma closedFormPair_single_inr {d : ℕ} (j : BivariateGrid d) :
    closedFormPair R d (Pi.single (.inr j) 1) =
      (0, monomial j.1.val (monomial j.2.val 1)) := by
  classical
  simp [closedFormPair, bivariateGridPolynomial, Pi.single_apply, apply_ite]

variable {d : ℕ} (f : R[X][X]) (i : ℕ × ℕ) (j : BivariateGrid d)

/-- An inner-derivative column is a scalar multiple of a single shifted coefficient. -/
lemma closedFormCoefficientMatrix_inl :
    closedFormCoefficientMatrix d f i (.inl j) =
      if j.1.val ≤ i.1 ∧ j.2.val ≤ i.2 + 1 then
        ((j.2.val : R) - (i.2 + 1 - j.2.val : ℕ)) * ((f.coeff (i.1 - j.1.val)).coeff (i.2 + 1 - j.2.val))
      else 0 := by
  change ((closedFormOperator f (closedFormPair R d (Pi.single (.inl j) 1))).coeff i.1).coeff i.2 = _
  simp only [closedFormPair_single_inl, closedFormOperator, LinearMap.coe_mk, AddHom.coe_mk,
    map_zero, zero_mul, sub_zero, add_zero, bivariateCoefficientDerivative_monomial,
    coeff_sub, coeff_monomial_mul_at]
  by_cases h : j.1.val ≤ i.1
  · simpa [h, derivative_monomial, coeff_bivariateCoefficientDerivative] using
      coeff_monomial_wronskian (f.coeff (i.1 - j.1.val)) (1 : R) j.2.val i.2
  · simp [h]

/-- The corresponding outer-derivative column has the opposite sign. -/
lemma closedFormCoefficientMatrix_inr :
    closedFormCoefficientMatrix d f i (.inr j) =
      if j.1.val ≤ i.1 + 1 ∧ j.2.val ≤ i.2 then
        -(((j.1.val : R) - (i.1 + 1 - j.1.val : ℕ)) * ((f.coeff (i.1 + 1 - j.1.val)).coeff (i.2 - j.2.val)))
      else 0 := by
  change ((closedFormOperator f (closedFormPair R d (Pi.single (.inr j) 1))).coeff i.1).coeff i.2 = _
  simp only [closedFormPair_single_inr, closedFormOperator, LinearMap.coe_mk, AddHom.coe_mk,
    map_zero, zero_mul, sub_zero, zero_sub]
  rw [← sub_eq_neg_add, ← neg_sub, coeff_neg, coeff_neg, coeff_monomial_wronskian]
  by_cases h : j.1.val ≤ i.1 + 1
  · simp only [h, ite_true, true_and]
    rw [← C_eq_natCast, ← C_eq_natCast, ← map_sub, monomial_mul_C, coeff_monomial_mul_at]
    split_ifs <;> simp
  · simp [h]

end

section

variable {R : Type*} [CommRing R] (d : ℕ) (f : R[X][X])
  (v : ClosedFormColumns d → R)
include R d f v

private lemma closedFormCoefficientMatrix_mulVec :
    closedFormCoefficientMatrix d f *ᵥ v =
      bivariateCoefficients R (closedFormOperator f (closedFormPair R d v)) := by
  exact congrArg (fun u => u v) (Matrix.toLin'_toMatrix' _)

/-- Matrix kernel membership is precisely the polynomial closed-form equation. -/
theorem closedFormCoefficientMatrix_kernel :
    closedFormCoefficientMatrix d f *ᵥ v = 0 ↔
      closedFormOperator f (closedFormPair R d v) = 0 := by
  rw [closedFormCoefficientMatrix_mulVec]
  exact bivariateCoefficients_injective.eq_iff' (map_zero _)

end

end
end CCDN
