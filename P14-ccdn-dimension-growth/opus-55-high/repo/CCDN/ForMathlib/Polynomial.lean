/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.RingTheory.Polynomial.Resultant.Basic

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

namespace Polynomial

section FiniteDifference

variable {K : Type*} [Field K] [CharZero K]

variable (P : K[X]) {m : ℕ} (hm : P.natDegree = m + 1) (s : K) (hs : s ≠ 0)
include hm hs

theorem natDegree_and_leadingCoeff_comp_X_add_C_sub_self
    :
    (P.comp (X + C s) - P).natDegree = m ∧
      (P.comp (X + C s) - P).leadingCoeff = P.leadingCoeff * (m + 1) * s := by
  have hP : P ≠ 0 := by grind
  have hhasse : (hasseDeriv m P).natDegree ≤ 1 := by
    have h := natDegree_hasseDeriv_le P m
    omega
  have hform := eq_X_add_C_of_natDegree_le_one hhasse
  have hcoeff : (P.comp (X + C s) - P).coeff m =
      P.leadingCoeff * (m + 1) * s := by
    rw [coeff_sub, ← taylor_apply, taylor_coeff, hform]
    simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff,
      zero_add, Nat.choose_self, Nat.cast_one, one_mul]
    rw [show 1 + m = m + 1 by omega, Nat.choose_succ_self_right, ← hm,
      coeff_natDegree]
    rw [hm, Nat.cast_add, Nat.cast_one]
    ring
  have hcoeff0 : (P.comp (X + C s) - P).coeff m ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (mul_ne_zero (leadingCoeff_ne_zero.mpr hP)
      (Nat.cast_add_one_ne_zero m)) hs
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

end FiniteDifference

variable {R : Type*}

/-- A polynomial whose degree `n` satisfies `(n : R) ≠ 0` has nonzero derivative. -/
theorem derivative_ne_zero_of_natCast_natDegree_ne_zero [Semiring R]
    [NoZeroDivisors R] {f : R[X]} (hn : (f.natDegree : R) ≠ 0) : derivative f ≠ 0 := by
  have hpos : 0 < f.natDegree := by
    rw [Nat.pos_iff_ne_zero]
    aesop
  intro hz
  have hc := congrArg (fun g => g.coeff (f.natDegree - 1)) hz
  rw [coeff_derivative, show f.natDegree - 1 + 1 = f.natDegree by omega, coeff_zero] at hc
  have he : ((f.natDegree - 1 : ℕ) : R) + 1 = f.natDegree := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel hpos]
  rw [he] at hc
  exact (mul_ne_zero (leadingCoeff_ne_zero.mpr (by grind)) hn) hc

/-- Divided differences agree with the derivative modulo the argument difference. -/
theorem exists_divided_difference [CommRing R]
    (f : R[X]) (y z : R) :
    ∃ q : R, f.eval y - f.eval z = (y - z) * q ∧
      y - z ∣ q - f.derivative.eval z := by
  have hd : X - C z ∣ f - C (f.eval z) := by
    rw [dvd_iff_isRoot]
    simp
  obtain ⟨g, hg⟩ := hd
  have he := congrArg (Polynomial.eval y) hg
  simp at he
  have hder := congrArg (fun p => p.derivative.eval z) hg
  simp at hder
  refine ⟨g.eval y, he, ?_⟩
  rw [hder]
  exact Polynomial.sub_dvd_eval_sub y z g

end Polynomial

namespace Matrix

open Polynomial

/-- The degree of a determinant of polynomials is at most the size times an entrywise degree
bound. -/
theorem natDegree_det_le {R ι : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R[X]) (D : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ D) :
    M.det.natDegree ≤ Fintype.card ι * D := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_smul_le _ _).trans
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _i : ι, D := Finset.sum_le_sum fun i _ => hM (σ i) i
    _ = _ := by simp

end Matrix

namespace Polynomial

/-- The degree in the coefficient parameter of a Sylvester resultant is at most the Sylvester
size times a coefficientwise degree bound. -/
theorem natDegree_resultant_le {R : Type*} [CommRing R]
    (f g : R[X][X]) (m n D : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ D)
    (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (f.resultant g m n).natDegree ≤ (m + n) * D := by
  have hM : ∀ i j, (f.sylvester g m n i j).natDegree ≤ D := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp [sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · grind
      · simp
    | right j =>
      simp [sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · grind
      · simp
  simpa [Fintype.card_fin, resultant] using Matrix.natDegree_det_le (f.sylvester g m n) D hM

