/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile

/-! The factorial and coefficient-count logarithms in the determinant
comparison cost only a dimension constant times s^(1+1/r). -/

namespace CCDN
noncomputable section

/-- The Hilbert function `s` of a degree-`d` hypersurface in `r + 2` homogeneous variables, given by
`s + C(r + 1 + (M - d), M - d) = C(r + 1 + M, M)`, is at least `M` when `0 < r` and
`0 < d ≤ M`. -/
lemma hypersurface_rank_ge_degree_parameter {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) : M ≤ s := by
  have hl := (Nat.mul_le_mul_left d (by
    calc
      _ = (M - d + 1).choose (M - d) := (Nat.choose_succ_self_right _).symm
      _ ≤ (r + (M - d)).choose (M - d) := Nat.choose_le_choose _ (by omega)
      _ = _ := Nat.choose_symm_add.symm)).trans (hypersurface_rank_binomial_bounds hdM hr).1
  have hk := Nat.mul_le_mul_right (M - d) (show 1 ≤ d from hd)
  have he := Nat.sub_add_cancel hdM
  nlinarith

/-- For `0 < r` and positive real `s`, `log s ≤ r * s ^ (1/r)`. -/
lemma log_le_dimension_root {r : ℕ} (hr : 0 < r) {s : ℝ} (hs : 0 < s) :
    Real.log s ≤ (r : ℝ) * s ^ (1 / (r : ℝ)) := by
  have hr0 : (0 : ℝ) < r := mod_cast hr
  have hh := Real.log_le_self (Real.rpow_nonneg hs.le (1 / r))
  rw [Real.log_rpow hs] at hh
  have hm := mul_le_mul_of_nonneg_left hh hr0.le
  have he : r * ((1 / r) * Real.log s) = Real.log s := by field_simp
  rwa [he] at hm

/-- The dimension constant `((r + 2) r + (r + 1)) / 2` bounding the archimedean logarithmic
terms of the determinant comparison by a multiple of `s ^ (1 + 1/r)`. -/
def hypersurfaceArchimedeanError (r : ℕ) : ℝ := ((r + 2 : ℝ) * r + (r + 1 : ℝ)) / 2

