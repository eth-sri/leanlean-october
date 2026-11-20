/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Finite differences, derivatives and resultants of univariate polynomials

## Main results

* `Polynomial.natDegree_comp_X_add_C_sub_self` and
  `Polynomial.leadingCoeff_comp_X_add_C_sub_self`: in characteristic zero, the finite difference
  `P(X + s) - P(X)` of a polynomial of degree `m + 1` with step `s ≠ 0` has degree `m` and
  leading coefficient `P.leadingCoeff * (m + 1) * s`.
* `Polynomial.derivative_ne_zero_of_natCast_natDegree_ne_zero`: a polynomial whose degree is
  nonzero in the coefficient ring has nonzero derivative.
* `Polynomial.exists_divided_difference`: the divided difference `(f(y) - f(z)) / (y - z)` exists
  and is congruent to `f'(z)` modulo `y - z`.
* `Matrix.natDegree_det_le`, `Polynomial.natDegree_resultant_le`: degree bounds for determinants
  and Sylvester resultants of polynomials in a coefficient parameter, independent of the
  eliminated variable.
* `Polynomial.resultant_ne_zero_of_irreducible_of_natDegree_lt`: padding the second Sylvester
  degree preserves nonvanishing when the first polynomial is irreducible.
-/

@[expose] public section

namespace Polynomial

section FiniteDifference

variable {K : Type*} [Field K] [CharZero K]

variable (P : K[X]) {m : ℕ} (hm : P.natDegree = m + 1) (s : K) (hs : s ≠ 0)

include hm hs in
private theorem natDegree_and_leadingCoeff_comp_X_add_C_sub_self :
    (P.comp (X + C s) - P).natDegree = m ∧
      (P.comp (X + C s) - P).leadingCoeff = P.leadingCoeff * (m + 1) * s := by
  have hP : P ≠ 0 := by
    grind
  have hhasse : (hasseDeriv m P).natDegree ≤ 1 := by
    grind [natDegree_hasseDeriv_le]
  have hcoeff : (P.comp (X + C s) - P).coeff m =
      P.leadingCoeff * (m + 1) * s := by
    rw [coeff_sub, ← taylor_apply, taylor_coeff, (eq_X_add_C_of_natDegree_le_one hhasse)]
    simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff,
      zero_add, Nat.choose_self, Nat.cast_one, one_mul]
    rw [show 1 + m = m + 1 by omega, Nat.choose_succ_self_right, ← hm,
      coeff_natDegree]
    rw [hm, Nat.cast_add, Nat.cast_one]
    ring
  have hcoeff0 : (P.comp (X + C s) - P).coeff m ≠ 0 := by
    grind [mul_ne_zero, leadingCoeff_ne_zero.mpr, Nat.cast_add_one_ne_zero]
  have hdiff0 : P.comp (X + C s) - P ≠ 0 := by
    intro h
    simp [h] at hcoeff0
  have hdeg : (P.comp (X + C s) - P).natDegree = m := by
    apply le_antisymm
    · have hlt := degree_sub_lt_right (degree_taylor P s) hP (leadingCoeff_taylor s P)
      change (P.comp (X + C s) - P).degree < P.degree at hlt
      rw [degree_eq_natDegree hdiff0, degree_eq_natDegree hP, Nat.cast_lt] at hlt
      omega
    · exact le_natDegree_of_ne_zero hcoeff0
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcoeff]⟩

include hm hs in
/-- In characteristic zero, the finite difference `P(X + s) - P(X)` with step `s ≠ 0` lowers
the degree by exactly one. -/
theorem natDegree_comp_X_add_C_sub_self : (P.comp (X + C s) - P).natDegree = m :=
  (natDegree_and_leadingCoeff_comp_X_add_C_sub_self P hm s hs).1

include hm hs in
/-- In characteristic zero, the finite difference `P(X + s) - P(X)` with step `s ≠ 0` of a
polynomial of degree `m + 1` has leading coefficient `P.leadingCoeff * (m + 1) * s`. -/
theorem leadingCoeff_comp_X_add_C_sub_self :
    (P.comp (X + C s) - P).leadingCoeff = P.leadingCoeff * (m + 1) * s :=
  (natDegree_and_leadingCoeff_comp_X_add_C_sub_self P hm s hs).2

end FiniteDifference

variable {R : Type*}

/-- A polynomial whose degree `n` satisfies `(n : R) ≠ 0` has nonzero derivative. -/
theorem derivative_ne_zero_of_natCast_natDegree_ne_zero [Semiring R]
    [NoZeroDivisors R] {f : R[X]} (hn : (f.natDegree : R) ≠ 0) : derivative f ≠ 0 := by
  have hpos : 0 < f.natDegree := by
    rw [Nat.pos_iff_ne_zero]
    aesop
  intro hz
  have hc := congrArg (fun g : R[X] => g.coeff (f.natDegree - 1)) hz
  rw [coeff_derivative, show f.natDegree - 1 + 1 = f.natDegree by omega, coeff_zero] at hc
  simp_all [← Nat.cast_add_one, Nat.sub_add_cancel hpos]

/-- Divided differences agree with the derivative modulo the argument difference. -/
theorem exists_divided_difference [CommRing R]
    (f : R[X]) (y z : R) :
    ∃ q : R, f.eval y - f.eval z = (y - z) * q ∧
      y - z ∣ q - f.derivative.eval z := by
  have hd : X - C z ∣ f - C (f.eval z) := by
    simp [dvd_iff_isRoot, IsRoot]
  obtain ⟨g, hg⟩ := hd
  have he := congrArg (Polynomial.eval y) hg
  simp only [eval_sub, eval_C, eval_mul, eval_X] at he
  have hder := congrArg (fun p : R[X] => p.derivative.eval z) hg
  simp only [derivative_sub, derivative_C, sub_zero, derivative_mul,
    derivative_X, derivative_sub, eval_add, eval_mul, eval_sub,
    eval_X, eval_C, sub_self, zero_mul, one_mul, add_zero] at hder
  refine ⟨g.eval y, he, ?_⟩
  rw [hder]
  exact Polynomial.sub_dvd_eval_sub y z g

end Polynomial

namespace Matrix

open Polynomial

end Matrix

namespace Polynomial

end Polynomial
