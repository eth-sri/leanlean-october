/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real

/-! Sharp leading constant for sums of surface standard-monomial degrees.
The numerical argument retains 2/3 of the cutoff in the weighted rank. -/

public section
namespace CCDN
open Finset

private lemma sum_successor_squares_lower (M : ℕ) :
    (M : ℝ) ^ 3 / 3 ≤ ∑ i ∈ range M, ((i : ℝ) + 1) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    grind [sum_range_succ]

/-- If `H k ≥ d * (k - d + 1) ^ 2 / 2` for all `k ≥ d`, then for `M ≥ d` the prefix sum
`∑ k < M, H k` is at least `d * (M - d) ^ 3 / 6`. -/
theorem surface_rank_prefix_sum_lower (H : ℕ → ℕ) {d M : ℕ} (hdM : d ≤ M)
    (hlower : ∀ k, d ≤ k →
      ↑d * ((k : ℝ) - d + 1) ^ 2 / 2 ≤ H k) :
    ↑d * (↑M - d) ^ 3 / 6 ≤ ∑ k ∈ range M, (H k : ℝ) := by
  have hsum : ↑d / 2 * ∑ i ∈ range (M - d), ((i : ℝ) + 1) ^ 2 ≤
      ∑ i ∈ range (M - d), (H (d + i) : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    have h := hlower (d + i) (by omega)
    push_cast at h
    convert h using 1
    ring
  have hnum := mul_le_mul_of_nonneg_left (sum_successor_squares_lower (M - d))
    (show 0 ≤ ↑d / 2 by positivity)
  rw [Nat.cast_sub hdM] at hnum
  have hprefix : (∑ i ∈ range (M - d), (H (d + i) : ℝ)) ≤
      ∑ k ∈ range M, (H k : ℝ) := by
    conv_rhs => rw [show M = d + (M - d) by omega, sum_range_add]
    exact le_add_of_nonneg_left (sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  convert (hnum.trans hsum).trans hprefix using 1
  ring

/-- Let `R ≥ 0` satisfy `d * R ^ 2 = 2 * s` and `M - d ≤ R ≤ M + 2`, where `0 < d ≤ M` and
`s ≥ 0`. If `W + d * (M - d) ^ 3 / 6 ≤ M * s`, then `W ≤ (2 / 3) * s * R + (2 * d + 2) * s`. -/
theorem surface_weight_root_bound {d M s W : ℝ}
    (hd : 0 < d) (hM : d ≤ M) (hs : 0 ≤ s) (R : ℝ) (hR : 0 ≤ R)
    (hroot : d * R ^ 2 = 2 * s)
    (hlo : M - d ≤ R) (hhi : R ≤ M + 2)
    (hweight : W + d * (M - d) ^ 3 / 6 ≤ M * s) :
    W ≤ (2 / 3 : ℝ) * s * R + (2 * d + 2) * s := by
  have ht := sub_nonneg.mpr hM
  have htR := pow_le_pow_left₀ ht hlo 2
  have hprod : R * (M - d) ≤ R ^ 2 := by nlinarith
  have hcube : R ^ 3 - (M - d) ^ 3 ≤ 3 * (d + 2) * R ^ 2 := by
    nlinarith
  nlinarith

end CCDN
