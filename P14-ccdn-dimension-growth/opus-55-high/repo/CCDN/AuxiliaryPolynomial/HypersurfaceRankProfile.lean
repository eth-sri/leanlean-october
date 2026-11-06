/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Bounds

/-! Uniform bounds for the exact homogeneous hypersurface Hilbert rank.
The factorial leading coefficient is retained in both directions. -/

namespace CCDN
section
open Finset

lemma sum_shifted_choose_add (r k d : ℕ) :
    (∑ i ∈ range d, (r + 1 + k + i).choose r) + (r + 1 + k).choose (r + 1) =
      (r + 1 + k + d).choose (r + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ]
    have hp := Nat.choose_succ_succ' (r + 1 + k + d) r
    rw [show r + 1 + k + (d + 1) = (r + 1 + k + d) + 1 by omega]
    omega

variable {r d M s : ℕ} (hdM : d ≤ M) (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M)
include hdM hr

/-- The exact rank is a sum of d adjacent binomial layers. -/
theorem hypersurface_rank_eq_sum
    :
    s = ∑ i ∈ range d, (r + 1 + (M - d) + i).choose r := by
  have hh := sum_shifted_choose_add r (M - d) d
  rw [show r + 1 + (M - d) + d = r + 1 + M by omega] at hh
  rw [← Nat.choose_symm_add,
    ← Nat.choose_symm_add] at hr
  omega

/-- The Hilbert function `s` of a degree-`d` hypersurface in `r + 2` homogeneous variables,
given by `s + C(r + 1 + (M - d), M - d) = C(r + 1 + M, M)`, satisfies
`d * C(r + (M - d), r) ≤ s ≤ d * C(r + M, r)`. -/
lemma hypersurface_rank_binomial_bounds
    :
    d * (r + (M - d)).choose r ≤ s ∧ s ≤ d * (r + M).choose r := by
  rw [hypersurface_rank_eq_sum hdM hr]
  constructor
  · calc
      _ = ∑ _i ∈ range d, (r + (M - d)).choose r := by simp
      _ ≤ _ := sum_le_sum fun i _ => Nat.choose_le_choose r (by omega)
  · calc
      _ ≤ ∑ _i ∈ range d, (r + M).choose r :=
        sum_le_sum fun i hi => Nat.choose_le_choose r (by grind)
      _ = _ := by simp

/-- Uniform power bounds with exact leading coefficient d/r!.
The error is controlled by shifts of at most d and r in the degree M. -/
theorem hypersurface_rank_power_bounds
    :
    (d : ℝ) * ((M : ℝ) - d + 1) ^ r / (r.factorial : ℝ) ≤ s ∧
      (s : ℝ) ≤ (d : ℝ) * ((M : ℝ) + r) ^ r / (r.factorial : ℝ) := by
  obtain ⟨hlo, hhi⟩ := hypersurface_rank_binomial_bounds hdM hr
  have hloR : (d : ℝ) * ((r + (M - d)).choose r : ℝ) ≤ s := mod_cast hlo
  have hhiR : (s : ℝ) ≤ (d : ℝ) * ((r + M).choose r : ℝ) := mod_cast hhi
  have hl : ((M : ℝ) - d + 1) ^ r / (r.factorial : ℝ) ≤ (r + (M - d)).choose r := by
    have h := Nat.pow_le_choose (α := ℝ) r (r + (M - d))
    rw [show r + (M - d) + 1 - r = M - d + 1 by omega] at h
    simp_all
  have hu : ((r + M).choose r : ℝ) ≤ (M + r) ^ r / r.factorial := by
    simpa [Nat.cast_add, add_comm] using Nat.choose_le_pow_div r (r + M)
  constructor
  · have h := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg d)
    grind
  · exact hhiR.trans
      (by simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg d))

