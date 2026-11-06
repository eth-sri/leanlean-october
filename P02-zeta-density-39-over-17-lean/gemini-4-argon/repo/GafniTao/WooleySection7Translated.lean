module
public import GafniTao.WooleySection7Valuation
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

/-!
# The translated and dilated top equations in Wooley Section 7

This file makes the substitutions in (7.9)--(7.10) literal.  Constants are
removed before taking tuple displacements, and every coefficient acquires
the exact factor `p^(a*i)` under `t ↦ p^a t`.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The top `r` normal-form equations `Phi_(k-r+l)` from (7.7), with Lean's
zero-based index `l`. -/
def wooleySection7TopSystem
    (k r p c : ℕ) (psi : Fin r → Polynomial ℤ) :
    WooleyPolynomialSystem r := fun l =>
  X ^ (wooleySection7Node k r l + 1) +
    C ((p : ℤ) ^ c) * X ^ (k + 1) * psi l

/-- Translation by `h`, dilation by `p^a`, and removal of the constant term.
This is the polynomial whose tuple displacement occurs in (7.10). -/
def wooleySection7TranslatedDilatedPolynomial
    (p a : ℕ) (h : ℤ) (phi : Polynomial ℤ) : Polynomial ℤ :=
  (taylor h phi).comp (C ((p : ℤ) ^ a) * X) - C (phi.eval h)

theorem wooleySection7TranslatedDilatedPolynomial_eval
    (p a : ℕ) (h y : ℤ) (phi : Polynomial ℤ) :
    (wooleySection7TranslatedDilatedPolynomial p a h phi).eval y =
      phi.eval ((p : ℤ) ^ a * y + h) - phi.eval h := by
  simp [wooleySection7TranslatedDilatedPolynomial, taylor_eval]

theorem wooleySection7TranslatedDilatedPolynomial_eq_comp
    (p a : ℕ) (h : ℤ) (phi : Polynomial ℤ) :
    wooleySection7TranslatedDilatedPolynomial p a h phi =
      (wooleyTaylorDifference h phi).comp (C ((p : ℤ) ^ a) * X) := by
  simp [wooleySection7TranslatedDilatedPolynomial,
    wooleyTaylorDifference]

theorem wooleySection7TranslatedDilatedPolynomial_coeff_zero
    (p a : ℕ) (h : ℤ) (phi : Polynomial ℤ) :
    (wooleySection7TranslatedDilatedPolynomial p a h phi).coeff 0 = 0 := by
  unfold wooleySection7TranslatedDilatedPolynomial
  rw [coeff_sub, comp_C_mul_X_coeff, coeff_C, pow_zero, mul_one,
    taylor_coeff]
  simp

/-- Exact coefficient scaling under the substitution in (7.9). -/
theorem wooleySection7TranslatedDilatedPolynomial_coeff_succ
    (p a i : ℕ) (h : ℤ) (phi : Polynomial ℤ) :
    (wooleySection7TranslatedDilatedPolynomial p a h phi).coeff (i + 1) =
      (taylor h phi).coeff (i + 1) *
        (p : ℤ) ^ (a * (i + 1)) := by
  unfold wooleySection7TranslatedDilatedPolynomial
  rw [coeff_sub, comp_C_mul_X_coeff, coeff_C]
  rw [ite_eq_right (by omega : i + 1 ≠ 0), sub_zero]
  rw [pow_mul]

/-- Constants cancel from equal-length tuple displacements, so evaluating
the translated polynomial is exactly the original top equation after (7.9). -/
theorem wooleySection7TranslatedDilatedPolynomial_tupleDisplacement
    {I : Type*} (p a R : ℕ) (h : ℤ) (phi : Polynomial ℤ)
    (point : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I) :
    wooleyIntegerTupleDisplacement R
        (fun x => phi.eval ((p : ℤ) ^ a * point x + h)) xy =
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleySection7TranslatedDilatedPolynomial p a h phi).eval
            (point x)) xy := by
  simp only [wooleyIntegerTupleDisplacement,
    wooleySection7TranslatedDilatedPolynomial_eval]
  simp_rw [sum_sub_distrib]
  ring_nf

/-- Coefficient form of the exact Omega expansion after simultaneously
performing the translation and the dilation in (7.9). -/
theorem wooleySection7TranslatedTop_coeff_rat
    {k r p c a : ℕ} (hrk : r ≤ k) (h : ℤ) (hh : h ≠ 0)
    (psi : Fin r → Polynomial ℤ) (i l : Fin r) :
    ((wooleySection7TranslatedDilatedPolynomial p a h
        (wooleySection7TopSystem k r p c psi l)).coeff
          ((i : ℕ) + 1) : ℚ) =
      (h : ℚ) ^
          (((wooleySection7Node k r l + 1 : ℕ) : ℤ) -
            ((((i : ℕ) + 1 : ℕ) : ℤ))) *
        (wooleySection7OmegaMatrix (p := p) (c := c)
          hrk h hh psi i l : ℚ) *
        (p : ℚ) ^ (a * ((i : ℕ) + 1)) := by
  rw [wooleySection7TranslatedDilatedPolynomial_coeff_succ]
  push_cast
  unfold wooleySection7TopSystem
  rw [(wooleySection7OmegaEntry_spec
    (p := p) (c := c) hrk h hh psi i l).1]
  rw [show
    (((wooleySection7Node k r l + 1 : ℕ) : ℤ) -
        ((((i : ℕ) + 1 : ℕ) : ℤ))) =
      (wooleySection7Node k r l : ℤ) - (i : ℤ) by omega]
  simp only [wooleySection7OmegaMatrix]
  ring_nf


