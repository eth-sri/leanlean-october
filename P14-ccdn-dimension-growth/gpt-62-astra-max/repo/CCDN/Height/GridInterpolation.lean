/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Lagrange

/-! Coarse coefficient control on the integer grid by Lagrange interpolation.
Only `(d+1)^(d+1)` is needed, as its logarithm is `O(d log d)`. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Finset

private lemma linear_mul_coefficient_bound {f : ℝ[X]} {H : ℝ}
    (hH : 0 ≤ H) (hf : ∀ k, ‖f.coeff k‖ ≤ H) (a b : ℝ) (k : ℕ) :
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

private lemma lagrange_product_bound (s : Finset ℕ) (i k : ℕ) :
    ‖(∏ j ∈ s, Lagrange.basisDivisor (i : ℝ) (j : ℝ)).coeff k‖ ≤
      ∏ j ∈ s, ((j : ℝ) + 1) / |(i : ℝ) - j| := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    by_cases hk : k = 0 <;> simp [coeff_one, hk]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have he : Lagrange.basisDivisor (i : ℝ) (j : ℝ) =
        C (((i : ℝ) - j)⁻¹) * X + C (-((i : ℝ) - j)⁻¹ * j) := by
      simp only [Lagrange.basisDivisor, neg_mul, map_neg, map_mul, sub_eq_add_neg]
      ring
    rw [he]
    have hh := linear_mul_coefficient_bound
      (show 0 ≤ ∏ l ∈ s, ((l : ℝ) + 1) / |(i : ℝ) - l| from
        Finset.prod_nonneg (fun _ _ => by positivity)) ih
      (((i : ℝ) - j)⁻¹) (-((i : ℝ) - j)⁻¹ * j) k
    convert hh using 1
    simp only [norm_inv, norm_mul, norm_neg, norm_natCast, Real.norm_eq_abs]
    ring

theorem polynomial_grid_coefficient_bound (f : ℝ[X]) {d : ℕ} (hd : f.natDegree ≤ d)
    {H : ℝ} (hH : 0 ≤ H) (heval : ∀ i : ℕ, i ≤ d → ‖f.eval (i : ℝ)‖ ≤ H) (k : ℕ) :
    ‖f.coeff k‖ ≤ (d+1 : ℝ)^(d+1) * H := by
  have hdeg : f.degree < (range (d+1)).card := by
    grind [card_range, degree_lt_iff_coeff_zero, coeff_eq_zero_of_natDegree_lt]
  conv_lhs => rw [Lagrange.eq_interpolate (Nat.cast_injective (R := ℝ)).injOn hdeg]
  rw [Lagrange.interpolate_apply,finsetSum_coeff]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ range (d+1), H * (d+1 : ℝ)^d := by
      apply sum_le_sum
      intro i hi
      rw [coeff_C_mul, norm_mul]
      refine mul_le_mul (heval i (by grind)) ((lagrange_product_bound _ _ k).trans ?_) (norm_nonneg _) hH
      calc
        _ ≤ ∏ _j ∈ (range (d+1)).erase i, (d+1 : ℝ) := by
          gcongr with j hj
          have h := mem_erase.mp hj
          have hden : (1 : ℝ) ≤ |(i:ℝ)-j| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast h.1.symm : (i:ℤ) ≠ j))
          apply (div_le_self (by positivity) hden).trans
          exact_mod_cast (by grind : j+1 ≤ d+1)
        _ = _ := by simp [card_erase_of_mem hi]
    _ = _ := by simp; ring

end
end CCDN
