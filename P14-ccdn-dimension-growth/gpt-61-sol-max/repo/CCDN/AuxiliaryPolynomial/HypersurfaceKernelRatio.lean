/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

import Mathlib

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The homogeneous kernel-to-rank ratio differs from its leading term by
at most 1/M. Exact binomial identities avoid a formal asymptotic expansion. -/

public section
namespace CCDN

private lemma shifted_choose_successor_identity (r k : ℕ) :
    (r + k + 1) * (r + k).choose r = (r + 1 + k).choose (r + 1) * (r + 1) := by
  grind [Nat.add_one_mul_choose_eq]

/-- Sharp leading term for the fraction of polynomial coefficients in the
homogeneous kernel, normalized by degree and rank. -/
theorem hypersurface_kernel_ratio_bounds {r d M s : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : HasHypersurfaceRank r d M s) :
    1 / (↑d * (r + 1 : ℝ)) - 1 / ↑M ≤
        ((r + 1 + (M - d)).choose (M - d) : ℝ) / (↑M * s) ∧
      ((r + 1 + (M - d)).choose (M - d) : ℝ) / (↑M * s) ≤
        1 / (↑d * (r + 1 : ℝ)) + 1 / ↑M := by
  obtain ⟨hlo, hhi⟩ := hypersurface_rank_binomial_bounds hdM hr
  have hs := lt_of_lt_of_le
    (Nat.mul_pos hd (Nat.choose_pos (by omega : r ≤ r + (M - d)))) hlo
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hd1 : 1 ≤ d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) < r + 1 := by positivity
  have hmd : (d : ℝ) ≤ M := by exact_mod_cast hdM
  let K : ℝ := (r + 1 + (M - d)).choose (M - d)
  let Qlo : ℝ := (r + (M - d)).choose r
  let Qhi : ℝ := (r + M).choose r
  have hlow : ↑d * Qlo ≤ s := by
    dsimp only [Qlo]
    exact_mod_cast hlo
  have hhigh : ↑s ≤ ↑d * Qhi := by
    dsimp only [Qhi]
    exact_mod_cast hhi
  have hK := by
    have hh := shifted_choose_successor_identity r (M - d)
    rw [Nat.choose_symm_add (a := r + 1) (b := M - d)] at hh
    have hhR := congrArg (fun x : ℕ => (x : ℝ)) hh
    push_cast [Nat.cast_sub hdM] at hhR
    exact hhR
  have hR := by
    have hh := shifted_choose_successor_identity r M
    rw [Nat.choose_symm_add (a := r + 1) (b := M), ← hr] at hh
    have hhR := congrArg (fun x : ℕ => (x : ℝ)) hh
    push_cast [Nat.cast_sub hdM] at hhR
    exact hhR
  change 1 / (↑d * (r + 1 : ℝ)) - 1 / ↑M ≤ K / (↑M * s) ∧
    K / (↑M * s) ≤ 1 / (↑d * (r + 1 : ℝ)) + 1 / ↑M
  constructor
  · apply (le_div_iff₀ (mul_pos hM0 hs0)).mpr
    field_simp
    nlinarith [mul_nonneg hr0.le hs0.le]
  · apply (div_le_iff₀ (mul_pos hM0 hs0)).mpr
    field_simp
    have hh : (↑r + 1) * s ≤ (d : ℝ) * (r + 1) * s := by
      simp_all
    nlinarith

end CCDN
