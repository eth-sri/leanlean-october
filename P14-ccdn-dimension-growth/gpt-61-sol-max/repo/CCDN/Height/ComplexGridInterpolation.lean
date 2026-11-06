/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Lagrange

/-! Sharp coefficient control from the integer grid. The absolute coefficient
sum of each Lagrange basis polynomial is at most a binomial coefficient;
summing gives the factor 3^d in CCDN Lemma 3.4.1, over the complex numbers. -/

public section
namespace CCDN
open Polynomial Finset

private lemma complex_linear_mul_coefficient_bound {f : ℂ[X]} {H : ℝ}
    (hH : 0 ≤ H) (hf : ∀ k, ‖f.coeff k‖ ≤ H) (a b : ℂ) (k : ℕ) :
    ‖((C a * X + C b) * f).coeff k‖ ≤ (‖a‖ + ‖b‖) * H := by
  rw [add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_C_mul]
  cases k with
  | zero =>
    simp only [coeff_X_mul_zero, mul_zero, zero_add, norm_mul]
    nlinarith [hf 0, norm_nonneg a, norm_nonneg b]
  | succ k =>
    rw [coeff_X_mul]
    have h := norm_add_le (a * f.coeff k) (b * f.coeff (k + 1))
    rw [norm_mul, norm_mul] at h
    have h₁ := mul_le_mul_of_nonneg_left (hf k) (norm_nonneg a)
    have h₂ := mul_le_mul_of_nonneg_left (hf (k + 1)) (norm_nonneg b)
    nlinarith

private lemma complex_nat_sub_norm (i j : ℕ) :
    ‖(i : ℂ) - j‖ = |(i : ℝ) - j| := by
  norm_cast

private lemma complex_lagrange_product_bound (s : Finset ℕ) (i k : ℕ) :
    ‖(∏ j ∈ s, Lagrange.basisDivisor ↑i (j : ℂ)).coeff k‖ ≤
      ∏ j ∈ s, (↑j + 1) / |(i : ℝ) - j| := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    aesop
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have he : Lagrange.basisDivisor ↑i (j : ℂ) =
        C (((i : ℂ) - j)⁻¹) * X + C (-((i : ℂ) - j)⁻¹ * j) := by
      simp only [Lagrange.basisDivisor, neg_mul, map_neg, map_mul, sub_eq_add_neg]
      ring
    rw [he]
    have hh := complex_linear_mul_coefficient_bound
      ((Finset.prod_nonneg (fun _ _ => by positivity))) ih
      ((↑i - j)⁻¹) (-((i : ℂ) - j)⁻¹ * j) k
    convert hh using 1
    simp only [norm_inv, norm_mul, norm_neg, norm_natCast, complex_nat_sub_norm]
    ring

private lemma integer_grid_lagrange_weight (d i : ℕ) (hi : i ≤ d) :
    (∏ j ∈ (range (d + 1)).erase i, (↑j + 1) / |(i : ℝ) - j|) =
      ((d + 1).choose (i + 1) : ℝ) := by
  classical
  induction d generalizing i with
  | zero =>
    simp_all
  | succ d ih =>
    by_cases hie : i = d + 1
    · subst i
      rw [range_add_one, erase_insert (by simp)]
      rw [prod_div_distrib]
      have hn : (∏ j ∈ range (d + 1), ((j : ℝ) + 1)) = ((d + 1).factorial : ℝ) := by
        exact_mod_cast (Finset.prod_range_add_one_eq_factorial (d + 1))
      have hd : (∏ j ∈ range (d + 1), |((d + 1 : ℕ) : ℝ) - j|) =
          ((d + 1).factorial : ℝ) := by
        calc
          _ = ∏ j ∈ range (d + 1), (((d + 1 - j : ℕ)) : ℝ) := by
            apply prod_congr rfl
            intro j hj
            have hj' := (mem_range.mp hj).le
            rw [Nat.cast_sub hj', abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hj'))]
          _ = _ := by
            exact_mod_cast (Nat.descFactorial_eq_prod_range (d + 1) (d + 1)).symm.trans
              (Nat.descFactorial_self (d + 1))
      rw [hn, hd, div_self (by positivity)]
      simp
    · have hid : i ≤ d := by omega
      have hne := Ne.symm hie
      rw [range_add_one, erase_insert_of_ne hne,
        prod_insert (by simp [mem_erase])]
      rw [ih i hid]
      have hlt : ↑i < (d : ℝ) + 1 := by exact_mod_cast (show i < d + 1 by omega)
      rw [Nat.cast_add, Nat.cast_one, abs_of_neg (by linarith)]
      have hc : ((d + 1).choose (i + 1) : ℝ) * (↑d + 2) =
          ((d + 2).choose (i + 1) : ℝ) * (↑d + 1 - i) := by
        have hh := Nat.choose_mul_succ_eq (d + 1) (i + 1)
        have hhR := congrArg (fun n : ℕ => (n : ℝ)) hh
        push_cast [Nat.cast_sub (show i ≤ d + 1 by omega)] at hhR
        convert hhR using 1
        ring
      have hden : ↑i - ((d : ℝ) + 1) ≠ 0 := by linarith
      field_simp
      nlinarith [hc]

private lemma two_pow_succ_sub_one_le_three_pow (d : ℕ) :
    (2 : ℝ) ^ (d + 1) - 1 ≤ 3 ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    grind [one_le_pow₀, pow_succ]

/-- CCDN Lemma 3.4.1 in coefficientwise form, with the exact factor 3^d. -/
theorem complex_polynomial_coefficient_bound_of_integer_grid
    (f : ℂ[X]) {d : ℕ} (hd : f.natDegree ≤ d) {H : ℝ} (hH : 0 ≤ H)
    (heval : ∀ i : ℕ, i ≤ d → ‖f.eval ↑i‖ ≤ H) (k : ℕ) :
    ‖f.coeff k‖ ≤ 3 ^ d * H := by
  have hinj : Set.InjOn (fun i : ℕ => (i : ℂ)) (range (d + 1)) :=
    Nat.cast_injective.injOn
  have hdeg : f.degree < (range (d + 1)).card := by
    grind [degree_lt_iff_coeff_zero, coeff_eq_zero_of_natDegree_lt]
  have he := Lagrange.eq_interpolate hinj hdeg
  have hb (i : ℕ) (hi : i ≤ d) :
      ‖(Lagrange.basis (range (d + 1)) (fun j : ℕ => (j : ℂ)) i).coeff k‖ ≤
        ((d + 1).choose (i + 1) : ℝ) := by
    have hh := complex_lagrange_product_bound ((range (d + 1)).erase i) i k
    rw [integer_grid_lagrange_weight d i hi] at hh
    exact hh
  have hs : (∑ i ∈ range (d + 1), ((d + 1).choose (i + 1) : ℝ)) =
      2 ^ (d + 1) - 1 := by
    have h := Nat.sum_range_choose (d + 1)
    rw [Finset.sum_range_succ'] at h
    have hh := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at hh
    norm_num at hh
    linarith
  conv_lhs => rw [he]
  rw [Lagrange.interpolate_apply, finsetSum_coeff]
  calc
    _ ≤ ∑ i ∈ range (d + 1), ‖(C (f.eval ↑i) *
        Lagrange.basis (range (d + 1)) (fun j : ℕ => (j : ℂ)) i).coeff k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ range (d + 1), H * ((d + 1).choose (i + 1) : ℝ) := by
      grind [sum_le_sum, norm_mul, mul_le_mul, norm_nonneg]
    _ = H * (2 ^ (d + 1) - 1) := by rw [← mul_sum, hs]
    _ ≤ H * 3 ^ d := mul_le_mul_of_nonneg_left (two_pow_succ_sub_one_le_three_pow d) hH
    _ = _ := mul_comm _ _

end CCDN
