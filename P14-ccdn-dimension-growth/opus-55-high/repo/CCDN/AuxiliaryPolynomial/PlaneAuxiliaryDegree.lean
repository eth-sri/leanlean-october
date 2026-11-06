/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Algebra.HomogeneousRankDichotomy
import CCDN.ForMathlib.Log

/-! Quantitative degree control from the plane determinant comparison. -/

namespace CCDN
open Real

section
variable {s d M : ℕ} (hd : 0 < d) (hdM : d ≤ M) (hr : 2 * s + d ^ 2 = d * (2 * M + 3))
include hd hdM hr

/-- The Hilbert function `s` of a plane curve of degree `d` in degree `M`, given by
`2 s + d² = d (2 M + 3)`, is at least `M` when `0 < d ≤ M`. -/
lemma plane_rank_ge_degree_parameter
    : M ≤ s := by
  have h := Nat.mul_le_mul_left (d - 1) hdM
  have he := Nat.sub_add_cancel hd
  nlinarith

/-- For the Hilbert function `s` of a plane curve of degree `d` in degree `M ≥ d`, the archimedean
terms `log s! / 2 + (s / 2) log C(M + 2, M)` of the determinant comparison are at most
`5 s² / 2`. -/
lemma plane_rank_archimedean_error
    :
    Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) ≤
      5 * (s : ℝ) ^ 2 / 2 := by
  have hMs := plane_rank_ge_degree_parameter hd hdM hr
  have hs := lt_of_lt_of_le (hd.trans_le hdM) hMs
  have hsR : (0 : ℝ) < s := mod_cast hs
  have hMR : (1 : ℝ) ≤ M := by bound
  have hMsR : (M : ℝ) ≤ s := mod_cast hMs
  have hl := (Real.log_le_sub_one_of_pos hsR).trans (by nlinarith)
  have hf : Real.log (s.factorial : ℝ) ≤ (s : ℝ) * Real.log s := by
    have hp : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := mod_cast Nat.factorial_le_pow s
    simpa using Real.log_le_log (by positivity) hp
  have hdim : 2 * ((2 + M).choose M : ℝ) = ((M : ℝ) + 2) * (M + 1) := by
    exact_mod_cast ternary_homogeneous_dimension M
  have hbound : ((2 + M).choose M : ℝ) ≤ ((M : ℝ) + 2) ^ 2 := by nlinarith
  have hlog : Real.log ((2 + M).choose M) ≤ 4 * s := by
    have h := Real.log_le_log (by
      exact_mod_cast Nat.choose_pos (show M ≤ 2 + M by omega)) hbound
    norm_num at h
    have h' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < M + 2 by positivity)
    nlinarith
  nlinarith

lemma plane_comparison_div_le {B L K X : ℝ}
    (hcomparison : (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d - X - K) ≤
      Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
        s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) :
    Real.log s - 4 * Real.log d - X - K ≤
      5 + 2 * M / s * Real.log B -
        2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 * Real.log L := by
  have hMs := plane_rank_ge_degree_parameter hd hdM hr
  have hsR : (0 : ℝ) < s := by bound
  have harch := plane_rank_archimedean_error hd hdM hr
  have hc : Real.log s - 4 * Real.log d - X - K ≤
      (Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
        s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) /
          ((s : ℝ) ^ 2 / 2) := (le_div_iff₀ (show (0 : ℝ) < (s : ℝ) ^ 2 / 2 by positivity)).mpr
    (by grind)
  calc
    _ ≤ _ := hc
    _ ≤ (5 * (s : ℝ) ^ 2 / 2 + s * M * Real.log B -
        (((2 + M).choose M : ℝ) - s) * Real.log L) / ((s : ℝ) ^ 2 / 2) := by
      gcongr
    _ = _ := by field_simp

/-- The small-height case of the plane auxiliary-degree calculation. The
coefficient obstruction is retained with its exact exponent 1/d². -/
theorem plane_auxiliary_log_degree_bound {B L A K : ℝ}
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hML : Real.log B ≤ M)
    (hheight : Real.log L ≤ 4 * d * Real.log B)
    (hcomparison : (s : ℝ) ^ 2 / 2 *
        (Real.log s - 4 * Real.log d - Real.log A - K) ≤
      Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
        s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) :
    Real.log M ≤ K + 23 + Real.log 2 + 3 * Real.log d + Real.log A +
      2 / d * Real.log B - Real.log L / (d : ℝ) ^ 2 := by
  have hdR : (0 : ℝ) < d := mod_cast hd
  have hMR : (0 : ℝ) < M := mod_cast hd.trans_le hdM
  have hdMR : (d : ℝ) ≤ M := mod_cast hdM
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hMs := plane_rank_ge_degree_parameter hd hdM hr
  have hsR : (0 : ℝ) < s := mod_cast lt_of_lt_of_le (hd.trans_le hdM) hMs
  have he : 2 * (s : ℝ) + (d : ℝ) ^ 2 = d * (2 * M + 3) := mod_cast hr
  have hslo : (d : ℝ) * M ≤ 2 * s := by nlinarith
  have hshi : (s : ℝ) ≤ d * (M + 1) := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hdim : 2 * ((2 + M).choose M : ℝ) = ((M : ℝ) + 2) * (M + 1) := by
    exact_mod_cast ternary_homogeneous_dimension M
  have hsquare : (s : ℝ) ^ 2 ≤ 2 * (d : ℝ) ^ 2 * ((2 + M).choose M) := by nlinarith
  have hlogB := Real.log_nonneg hB
  have hlogL := Real.log_nonneg hL
  have hbasic := plane_comparison_div_le hd hdM hr hcomparison
  have hbox : 2 * (M : ℝ) / s * Real.log B ≤ 2 / d * Real.log B + 2 := by
    have hrat : 2 * (M : ℝ) / s ≤ 2 / d + 2 / M := by
      apply (div_le_iff₀ hsR).mpr
      field_simp
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hrat hlogB
    have hrem : 2 / (M : ℝ) * Real.log B ≤ 2 := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hMR).mpr (by linarith)
    nlinarith
  have hcoef : Real.log L / d ^ 2 - 16 ≤
      2 * (((2 + M).choose M : ℝ) - s) / s ^ 2 * Real.log L := by
    have hrat : 1 / d ^ 2 - 2 / s ≤
        2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 := by
      apply (le_div_iff₀ (show (0 : ℝ) < (s : ℝ) ^ 2 by positivity)).mpr
      field_simp
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hrat hlogL
    have hrem : 2 / s * Real.log L ≤ 16 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hsR).mpr
      have hh := mul_le_mul_of_nonneg_left hML hdR.le
      nlinarith
    simp [sub_mul, one_div, inv_mul_eq_div] at hh
    linarith
  have hlogs : Real.log d + Real.log M - Real.log 2 ≤ Real.log s := by
    have h := Real.log_le_log (show (0 : ℝ) < d * M / 2 by positivity)
      (show (d : ℝ) * M / 2 ≤ s by linarith)
    rwa [Real.log_div (by positivity) (by norm_num), Real.log_mul hdR.ne' hMR.ne'] at h
  linarith

end

/-- Exponentiation of the logarithmic degree bound, keeping the coefficient
saving and the leading box exponent unchanged. -/
lemma plane_degree_bound_of_log_bound {d M : ℕ} {B L A K : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hB : 0 < B) (hL : 0 < L) (hA : 0 < A)
    (hlog : Real.log M ≤ K + 23 + Real.log 2 + 3 * Real.log d + Real.log A +
      2 / d * Real.log B - Real.log L / (d : ℝ) ^ 2) :
    (M : ℝ) ≤ 2 * Real.exp (K + 23) * (d : ℝ) ^ 3 * A * B ^ (2 / (d : ℝ)) /
      L ^ (1 / (d : ℝ) ^ 2) := by
  have hdR : (0 : ℝ) < d := mod_cast hd
  refine Real.natCast_le_of_log_le_log hM (by positivity) ?_
  rw [Real.log_div (by positivity) (by positivity)]
  simp only [Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (Real.exp_pos _).ne',
    Real.log_mul (by positivity : 2 * Real.exp (K + 23) ≠ 0) (by positivity : (d : ℝ) ^ 3 ≠ 0),
    Real.log_mul (by positivity : 2 * Real.exp (K + 23) * (d : ℝ) ^ 3 ≠ 0) hA.ne',
    Real.log_mul (by positivity : 2 * Real.exp (K + 23) * (d : ℝ) ^ 3 * A ≠ 0)
      (Real.rpow_pos_of_pos hB _).ne', Real.log_exp, Real.log_pow, Real.log_rpow hB,
    Real.log_rpow hL]
  convert hlog using 1
  push_cast
  ring

