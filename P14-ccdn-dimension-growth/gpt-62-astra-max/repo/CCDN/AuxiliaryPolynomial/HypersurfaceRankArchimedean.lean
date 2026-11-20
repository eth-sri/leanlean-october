/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile

/-! The factorial and coefficient-count logarithms in the determinant
comparison cost only a dimension constant times s^(1+1/r). -/

@[expose] public section
namespace CCDN
noncomputable section

variable {r d M s : ℕ} (hr : 0 < r)

/-- The Hilbert function `s` of a degree-`d` hypersurface in `r + 2` homogeneous variables, given by
`s + C(r + 1 + (M - d), M - d) = C(r + 1 + M, M)`, is at least `M` when `0 < r` and
`0 < d ≤ M`. -/
lemma hypersurface_rank_ge_degree_parameter
    (hrpos : 0 < r) (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) : M ≤ s := by
  have hc : M - d + 1 ≤ (r + (M - d)).choose r := by
    calc
      _ = (M - d + 1).choose (M - d) := (Nat.choose_succ_self_right _).symm
      _ ≤ (r + (M - d)).choose (M - d) := Nat.choose_le_choose _ (by omega)
      _ = _ := Nat.choose_symm_add.symm
  have hl := (Nat.mul_le_mul_left d hc).trans (hypersurface_rank_binomial_bounds hdM hr).1
  have hk := Nat.mul_le_mul_right (M - d) (show 1 ≤ d from hd)
  have he := Nat.sub_add_cancel hdM
  nlinarith

include hr in
/-- For `0 < r` and positive real `s`, `log s ≤ r * s ^ (1/r)`. -/
lemma log_le_dimension_root {s : ℝ} (hs : 0 < s) :
    Real.log s ≤ (r : ℝ) * s ^ (1 / (r : ℝ)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hh := Real.log_le_self (Real.rpow_nonneg hs.le (1 / (r : ℝ)))
  rw [Real.log_rpow hs] at hh
  have hm := mul_le_mul_of_nonneg_left hh hr0.le
  have he : (r : ℝ) * ((1 / (r : ℝ)) * Real.log s) = Real.log s := by field_simp
  rwa [he] at hm

include hr in
/-- Stirling's crude bound suffices after normalizing by the determinant rank. -/
theorem log_factorial_rank_le (hs : 0 < s) :
    Real.log (s.factorial : ℝ) ≤ r * (s : ℝ) ^ (1 + 1 / (r : ℝ)) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h : (s.factorial : ℝ) ≤ (s : ℝ)^s := by exact_mod_cast Nat.factorial_le_pow s
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at hl
  rw [Real.rpow_add hs0, Real.rpow_one, mul_left_comm]
  exact hl.trans (mul_le_mul_of_nonneg_left (log_le_dimension_root hr hs0) hs0.le)

end
end CCDN
