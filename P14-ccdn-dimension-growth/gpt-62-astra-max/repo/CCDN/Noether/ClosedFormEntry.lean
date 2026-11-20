/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Noether.BivariateCoefficientMatrix


@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Matrix

section
variable {R : Type*} [CommRing R] (d : ℕ) (i : BivariateGrid d)

/-- The `k`-th coefficient of `monomial n a * f` is `a * f.coeff (k - n)` if `n ≤ k` and zero
otherwise. -/
lemma coeff_monomial_mul_at
    (f : R[X]) (a : R) (n k : ℕ) :
    (monomial n a * f).coeff k = if n ≤ k then a * f.coeff (k - n) else 0 := by
  rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs <;> simp_all

private lemma bivariateGridPolynomial_single (a : R) :
    bivariateGridPolynomial R d (Pi.single i a) =
      monomial i.1.val (monomial i.2.val a) := by
  classical
  simp [bivariateGridPolynomial, Pi.single_apply, apply_ite]

/-- The standard basis vector of the first block decodes to the pair `(monomial, 0)` with the
corresponding grid monomial. -/
lemma closedFormPair_single_inl :
    closedFormPair R d (Pi.single (.inl i) 1) =
      (monomial i.1.val (monomial i.2.val 1), 0) := by
  classical
  apply Prod.ext
  · change bivariateGridPolynomial R d _ = _
    convert bivariateGridPolynomial_single d i (1 : R) using 1
    congr 1
    ext j
    simp [Pi.single_apply]
  solve_by_elim [map_zero]

/-- The standard basis vector of the second block decodes to the pair `(0, monomial)` with the
corresponding grid monomial. -/
lemma closedFormPair_single_inr :
    closedFormPair R d (Pi.single (.inr i) 1) =
      (0, monomial i.1.val (monomial i.2.val 1)) := by
  classical
  apply Prod.ext
  solve_by_elim [map_zero]
  · change bivariateGridPolynomial R d _ = _
    convert bivariateGridPolynomial_single d i (1 : R) using 1
    congr 1
    ext j
    simp [Pi.single_apply]

end

variable {R : Type*} [CommRing R]

private lemma exponent_diff (a i : ℕ) (u : ℕ → R) :
    (if a-1 ≤ i then (a:R)*u (i-(a-1)) else 0) -
      (if a ≤ i then u (i-a+1) * ((i-a:ℕ)+1:R) else 0) =
    (if a ≤ i+1 then (a:R)-((i+1-a:ℕ):R) else 0)*u (i+1-a) := by
  cases a with
  | zero => simp; ring
  | succ a =>
    rcases lt_trichotomy a i with h|rfl|h
    · have e : i-(a+1)+1=i-a := by omega
      simp [h.le,Nat.succ_le_of_lt h,e]
      ring
    · simp
    · simp [h.not_ge,show ¬ a + 1 ≤ i by omega]

private lemma outer_deriv_coeff (f : R[X][X]) (i j : ℕ) :
    (f.derivative.coeff i).coeff j = (f.coeff (i+1)).coeff j*((i:R)+1) := by
  rw [coeff_derivative, show (i:R[X])+1=C ((i:R)+1) by simp,coeff_mul_C]

/-- The two derivatives in a column select the *same* coefficient of the
plane equation. Store its bidegree and the signed difference of exponents. -/
def closedFormEntry {d : ℕ} (i : ℕ × ℕ) : ClosedFormColumns d → (ℕ × ℕ) × ℤ
  | .inl (a,b) => ((i.1-a,i.2+1-b), if a ≤ i.1 ∧ b ≤ i.2+1 then (b:ℤ) - ((i.2+1-b:ℕ):ℤ) else 0)
  | .inr (a,b) => ((i.1+1-a,i.2-b), if a ≤ i.1+1 ∧ b ≤ i.2 then ((i.1+1-a:ℕ):ℤ) - (a:ℤ) else 0)

variable {d : ℕ} (f : R[X][X])

private lemma bi_shift (a b i j : ℕ) (c : R) :
    ((monomial a (monomial b c)*f).coeff i).coeff j = if a ≤ i ∧ b ≤ j then c*(f.coeff (i-a)).coeff (j-b) else 0 := by
  rw [coeff_monomial_mul_at]; split_ifs <;> simp_all [coeff_monomial_mul_at]

lemma closedFormEntry_apply (i : ℕ × ℕ) (c : ClosedFormColumns d) :
    closedFormCoefficientMatrix d f i c = let (u,w) := closedFormEntry i c
      (w:R)*(f.coeff u.1).coeff u.2 := by
  classical
  change ((closedFormOperator f (closedFormPair R d (Pi.single c 1))).coeff i.1).coeff i.2 = _
  rcases i with ⟨i,j⟩; rcases c with ⟨⟨a,ha⟩,⟨b,hb⟩⟩|⟨⟨a,ha⟩,⟨b,hb⟩⟩
  · rw [closedFormPair_single_inl]; simp only [closedFormOperator,LinearMap.coe_mk,AddHom.coe_mk,
      bivariateCoefficientDerivative_monomial,map_zero,zero_mul,one_mul,sub_zero,add_zero,
      coeff_sub,bi_shift,closedFormEntry,coeff_bivariateCoefficientDerivative,coeff_derivative]
    by_cases hi : a ≤ i
    · simpa [hi,apply_ite (fun k : ℤ => (k:R))] using exponent_diff b j (fun l => (f.coeff (i-a)).coeff l)
    · simp [hi]
  · rw [closedFormPair_single_inr]; simp only [closedFormOperator,LinearMap.coe_mk,AddHom.coe_mk,
      bivariate_derivative_monomial,map_zero,zero_mul,one_mul,sub_self,zero_sub,
      coeff_neg,coeff_add,bi_shift,closedFormEntry,outer_deriv_coeff]
    by_cases hj : b ≤ j
    · have h := congrArg Neg.neg (exponent_diff a i (fun k => (f.coeff k).coeff (j-b)))
      by_cases ha : a ≤ i+1
      · simp [hj,ha] at h ⊢; linear_combination h
      · simp [hj,ha,show ¬ a ≤ i by omega]
    · simp [hj]

end
end CCDN
