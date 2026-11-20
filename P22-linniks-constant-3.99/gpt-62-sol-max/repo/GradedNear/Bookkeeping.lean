module

public import Mathlib

@[expose] public section

namespace GradedNear

open Finset

variable {ι : Type*} [Fintype ι]

/-- A symmetric nonnegative pair excess costs its row sum on the diagonal. -/
lemma quadratic_rows (M P : ι → ι → ℝ) (a d : ι → ℝ) (c : ℝ) (ha : ∀ j, 0 ≤ a j)
    (hP : ∀ j k, 0 ≤ P j k) (hsym : ∀ j k, P j k = P k j) [DecidableEq ι]
    (hM : ∀ j k, M j k ≤ (if k = j then d j else 0) + c + P j k) :
    ∑ j, ∑ k, a j * a k * M j k ≤
      ∑ j, (d j + ∑ k, P j k) * a j ^ 2 + c * (∑ j, a j) ^ 2 := by
  have hswap : ∑ j, ∑ k, P j k * a k ^ 2 = ∑ j, ∑ k, P j k * a j ^ 2 := by
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by rw [hsym]
  calc
    _ ≤ ∑ j, ∑ k, ((if k = j then d j * a j ^ 2 else 0) + c * a j * a k +
        (P j k * a j ^ 2 + P j k * a k ^ 2) / 2) := by
      refine sum_le_sum fun j _ => sum_le_sum fun k _ => ?_
      have h := mul_le_mul_of_nonneg_left (hM j k) (mul_nonneg (ha j) (ha k))
      have h' := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (a j) (a k)) (hP j k)
      split_ifs at h ⊢ <;> (try subst k) <;> nlinarith only [h, h']
    _ = _ := by
      simp only [sum_add_distrib, ← sum_div, sum_ite_eq', mem_univ, ite_true, hswap, add_self_div_two]
      simp only [add_mul, sum_add_distrib, ← mul_sum, ← sum_mul]
      ring

end GradedNear
