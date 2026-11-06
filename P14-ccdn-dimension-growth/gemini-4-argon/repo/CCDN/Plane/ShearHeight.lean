/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.ShearNormalization

/-! Explicit coefficient-height bounds for the bounded integral shear. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- For the selected parameter 0<=a<=d, the sheared height is at most
H*(d+1)^(d+2), hence its logarithm costs only O(d log d). -/
theorem bivariateShear_bounded_coefficient_bound (a d : ℕ) (ha : a ≤ d)
    (f : ℤ[X][X]) (hd : bivariateTotalDegree f ≤ d)
    (H : ℝ) (hH : 0 ≤ H) (hf : BivariateCoefficientBound f H) :
    BivariateCoefficientBound (bivariateShear ℤ (a : ℤ) f) (((d : ℝ) + 1) ^ (d + 2) * H) := by
  classical
  have hpow (n : ℕ) : BivariateCoefficientBound ((C X + C (C (a : ℤ)) * X : ℤ[X][X]) ^ n)
      ((1 + |((a : ℤ) : ℝ)|) ^ n) := by
    induction n with
    | zero =>
      intro i j
      by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [coeff_one, hi, hj]
    | succ n ih =>
      rw [pow_succ', pow_succ']
      have h₁ := bivariateCoefficientBound_monomial_mul (by positivity) ih 1 0 1
      have h₂ := bivariateCoefficientBound_monomial_mul (by positivity) ih (a : ℤ) 1 0
      have hh : BivariateCoefficientBound
          (monomial 0 (monomial 1 (1 : ℤ)) * (C X + C (C (a : ℤ)) * X) ^ n +
            monomial 1 (monomial 0 (a : ℤ)) * (C X + C (C (a : ℤ)) * X) ^ n)
          (|((1 : ℤ) : ℝ)| * (1 + |((a : ℤ) : ℝ)|) ^ n +
            |((a : ℤ) : ℝ)| * (1 + |((a : ℤ) : ℝ)|) ^ n) := fun i j => by
        simp only [coeff_add, Int.cast_add]
        exact (abs_add_le _ _).trans (add_le_add (h₁ i j) (h₂ i j))
      rw [show monomial 0 (monomial 1 (1 : ℤ)) * (C X + C (C (a : ℤ)) * X) ^ n +
          monomial 1 (monomial 0 (a : ℤ)) * (C X + C (C (a : ℤ)) * X) ^ n =
          (C X + C (C (a : ℤ)) * X) * (C X + C (C (a : ℤ)) * X) ^ n by
        simp only [← C_mul_X_pow_eq_monomial, pow_zero, pow_one, map_one, one_mul, mul_one]; ring] at hh
      convert hh using 1
      simp only [Int.cast_one, abs_one, one_mul]; ring
  have hX : bivariateShear ℤ (a : ℤ) (X : ℤ[X][X]) = X := by
    rw [← bivariatePolynomialEquiv_X_zero, bivariateShear_equiv]
    change bivariatePolynomialEquiv ℤ (MvPolynomial.aeval _ (MvPolynomial.X 0)) = _
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_zero, bivariatePolynomialEquiv_X_zero]
  have hCX : bivariateShear ℤ (a : ℤ) (C X : ℤ[X][X]) = C X + C (C (a : ℤ)) * X := by
    rw [← bivariatePolynomialEquiv_X_one, bivariateShear_equiv]
    change bivariatePolynomialEquiv ℤ (MvPolynomial.aeval _ (MvPolynomial.X 1)) = _
    simp only [MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add, map_mul,
      bivariatePolynomialEquiv_X_one, bivariatePolynomialEquiv_X_zero, bivariatePolynomialEquiv_C]
  have he := bivariateGridPolynomial_reconstruct (d + 1) f
    (inBivariateGrid_of_totalDegree_lt _ _ (by omega))
  change (∑ k : BivariateGrid (d + 1),
    monomial k.1.val (monomial k.2.val ((f.coeff k.1.val).coeff k.2.val))) = f at he
  have hb (k : BivariateGrid (d + 1)) :
      BivariateCoefficientBound
        (bivariateShear ℤ (a : ℤ) (monomial k.1.val (monomial k.2.val ((f.coeff k.1.val).coeff k.2.val))))
        (H * ((d : ℝ) + 1) ^ d) := by
    let c := (f.coeff k.1.val).coeff k.2.val
    have hmon : bivariateShear ℤ (a : ℤ) (monomial k.1.val (monomial k.2.val c)) =
        monomial k.1.val (monomial 0 c) * (C X + C (C (a : ℤ)) * X) ^ k.2.val := by
      rw [show monomial k.1.val (monomial k.2.val c) =
          C (C c) * (X : ℤ[X][X]) ^ k.1.val * (C X) ^ k.2.val by
        rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]; simp only [map_mul, map_pow]; ring,
        map_mul, map_mul, map_pow, map_pow, hX, hCX,
        show bivariateShear ℤ (a : ℤ) (C (C c)) = C (C c) from (bivariateShear ℤ (a : ℤ)).commutes c]
      simp only [← C_mul_X_pow_eq_monomial, pow_zero, mul_one]
    refine bivariateCoefficientBound_mono (hmon.symm ▸
      bivariateCoefficientBound_monomial_mul (by positivity) (hpow k.2.val) c k.1.val 0) ?_
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) a)]
    have haR : (a : ℝ) ≤ d := mod_cast ha
    exact mul_le_mul (hf _ _) ((pow_le_pow_right₀ (by linarith) (by omega : k.2.val ≤ d)).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) d)) (by positivity) hH
  intro r s
  rw [← he, map_sum]
  simp only [finsetSum_coeff, Int.cast_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum fun k _ => hb k r s).trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, BivariateGrid, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_add]
  ring

end
end CCDN
