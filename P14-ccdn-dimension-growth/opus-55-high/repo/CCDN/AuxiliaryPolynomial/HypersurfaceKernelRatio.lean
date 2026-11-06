/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The homogeneous kernel-to-rank ratio differs from its leading term by
at most 1/M. Exact binomial identities avoid a formal asymptotic expansion. -/

namespace CCDN
section

lemma shifted_choose_successor_identity (r k : ℕ) :
    (r + k + 1) * (r + k).choose r = (r + 1 + k).choose (r + 1) * (r + 1) := by
  rw [show r + 1 + k = r + k + 1 by omega]
  exact Nat.add_one_mul_choose_eq (r + k) r

/-- Sharp leading term for the fraction of polynomial coefficients in the
homogeneous kernel, normalized by degree and rank. -/
theorem hypersurface_kernel_ratio_bounds {r d M s : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M) :
    1 / ((d : ℝ) * (r + 1 : ℝ)) - 1 / (M : ℝ) ≤
        ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) ∧
      ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) ≤
        1 / ((d : ℝ) * (r + 1 : ℝ)) + 1 / (M : ℝ) := by
  obtain ⟨hlo, hhi⟩ := hypersurface_rank_binomial_bounds hdM hr
  have hs := lt_of_lt_of_le
    (Nat.mul_pos hd (Nat.choose_pos (by grind))) hlo
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hs0 : (0 : ℝ) < s := mod_cast hs
  have hM0 : (0 : ℝ) < M := mod_cast hd.trans_le hdM
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hr0 : (0 : ℝ) < r + 1 := by positivity
  have hmd : (d : ℝ) ≤ M := mod_cast hdM
  let K : ℝ := (r + 1 + (M - d)).choose (M - d)
  let Qlo : ℝ := (r + (M - d)).choose r
  let Qhi : ℝ := (r + M).choose r
  have hlow : (d : ℝ) * Qlo ≤ s := by
    dsimp [Qlo]
    exact_mod_cast hlo
  have hhigh : (s : ℝ) ≤ (d : ℝ) * Qhi := by
    dsimp [Qhi]
    exact_mod_cast hhi
  have hK : ((r : ℝ) + (M - d) + 1) * Qlo = K * (r + 1) := by
    have hh := shifted_choose_successor_identity r (M - d)
    rw [Nat.choose_symm_add (a := r + 1) (b := M - d)] at hh
    have hhR := congrArg (fun x : ℕ => (x : ℝ)) hh
    push_cast [Nat.cast_sub hdM] at hhR
    exact hhR
  have hR : ((r : ℝ) + M + 1) * Qhi = ((s : ℝ) + K) * (r + 1) := by
    have hh := shifted_choose_successor_identity r M
    rw [Nat.choose_symm_add (a := r + 1) (b := M), ← hr] at hh
    have hhR := congrArg (fun x : ℕ => (x : ℝ)) hh
    grind
  have hKmul : (d : ℝ) * (r + 1) * K ≤ ((M : ℝ) + r + 1) * s := by nlinarith
  have hRmul : ((M : ℝ) + r + 1) * s ≤ (d : ℝ) * (r + 1) * ((s : ℝ) + K) := by
    nlinarith
  change 1 / (d * (r + 1 : ℝ)) - 1 / M ≤ K / (M * s) ∧
    K / (M * s) ≤ 1 / (d * (r + 1 : ℝ)) + 1 / M
  constructor
  · apply (le_div_iff₀ (mul_pos hM0 hs0)).mpr
    field_simp
    nlinarith
  · apply (div_le_iff₀ (mul_pos hM0 hs0)).mpr
    field_simp
    nlinarith

