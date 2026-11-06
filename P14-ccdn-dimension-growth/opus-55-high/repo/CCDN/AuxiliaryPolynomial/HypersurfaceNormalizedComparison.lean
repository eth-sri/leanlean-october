/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean
import CCDN.Determinant.HypersurfaceHeightDeterminant
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightComparison

/-! The normalized higher-dimensional determinant inequality, retaining the
exact root-rank and kernel-rank coefficients needed for uniform degree selection. -/

namespace CCDN
noncomputable section
open MvPolynomial

/-- Absorb the archimedean rank terms and divide by Ms. No fixed-factor
approximation of the leading rank or coefficient-height term is made. -/
theorem hypersurface_rank_comparison_normalized {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M)
    (B L A E : ℝ)
    (hcomparison : (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (r : ℝ)) *
          (Real.log s - (r : ℝ) * (4 * Real.log d + Real.log A) - E) ≤
      Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((r + 1 + M).choose M : ℝ) +
        s * M * Real.log B - (((r + 1 + M).choose M : ℝ) - s) * Real.log L) :
    (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) / ((r + 1 : ℝ) * M) *
      (Real.log s - (r : ℝ) * (4 * Real.log d + Real.log A) -
        (E + (r + 1 : ℝ) * hypersurfaceArchimedeanError r / (r.factorial : ℝ) ^ (1 / (r : ℝ)))) ≤
      Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) * Real.log L := by
  have hMs := hypersurface_rank_ge_degree_parameter hrpos hd hdM hr
  have hs0 : (0 : ℝ) < s := mod_cast lt_of_lt_of_le (hd.trans_le hdM) hMs
  have hM0 : (0 : ℝ) < M := mod_cast hd.trans_le hdM
  have hr1 : (r + 1 : ℝ) ≠ 0 := by positivity
  have hfac : r.factorial ^ (1 / r) ≠ 0 := by positivity
  have harch : Real.log s.factorial / 2 + s / 2 * Real.log ((r + 1 + M).choose M : ℝ) ≤
      hypersurfaceArchimedeanError r * (s : ℝ) ^ (1 + 1 / (r : ℝ)) := by
    have hs := lt_of_lt_of_le (hd.trans_le hdM) hMs
    have hs0 : (0 : ℝ) < s := mod_cast hs
    have hf : Real.log s.factorial ≤ s * Real.log s := by
      have hh : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := mod_cast Nat.factorial_le_pow s
      simpa using Real.log_le_log (by positivity) hh
    have hlog : Real.log ((r + 1 + M).choose M : ℝ) ≤ (r + 1 : ℝ) * (Real.log 2 + Real.log s) := by
      have hs : (1 : ℝ) ≤ s := mod_cast lt_of_lt_of_le (hd.trans_le hdM) hMs
      have hdim : (r + 1 + M).choose M ≤ (M + 1) ^ (r + 1) := by
        rw [← Nat.choose_symm_add, Nat.add_comm (r + 1) M]
        exact Nat.choose_add_le_add_one_pow M (r + 1)
      have hdimR : ((r + 1 + M).choose M : ℝ) ≤ ((M : ℝ) + 1) ^ (r + 1) := mod_cast hdim
      have hMsR : (M : ℝ) ≤ s := mod_cast hMs
      have hbound : ((r + 1 + M).choose M : ℝ) ≤ (2 * (s : ℝ)) ^ (r + 1) :=
        hdimR.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
      have hh := Real.log_le_log (by
        exact_mod_cast Nat.choose_pos (by grind)) hbound
      rw [Real.log_pow, Real.log_mul (by norm_num) (by grind)] at hh
      simpa using hh
    have hlroot := log_le_dimension_root hrpos hs0
    have hroot1 : 1 ≤ (s : ℝ) ^ (1 / (r : ℝ)) := Real.one_le_rpow (mod_cast hs) (by positivity)
    have hl2 : Real.log 2 ≤ 1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hdim : Real.log ((r + 1 + M).choose M : ℝ) ≤
        (r + 1 : ℝ) * ((r + 1 : ℝ) * (s : ℝ) ^ (1 / (r : ℝ))) := by
      have hh := mul_le_mul_of_nonneg_left hlroot (show 0 ≤ (r + 1 : ℝ) by positivity)
      have h2 := mul_le_mul_of_nonneg_left (hl2.trans hroot1) (show 0 ≤ (r + 1 : ℝ) by positivity)
      nlinarith
    have hfac := mul_le_mul_of_nonneg_left hlroot hs0.le
    have hdim' := mul_le_mul_of_nonneg_left hdim (show 0 ≤ (s : ℝ) / 2 by positivity)
    rw [Real.rpow_add hs0, Real.rpow_one]
    unfold hypersurfaceArchimedeanError
    nlinarith
  have hkernel : ((r + 1 + M).choose M : ℝ) - s = (r + 1 + (M - d)).choose (M - d) := by
    have hh : (s : ℝ) + ((r + 1 + (M - d)).choose (M - d) : ℝ) = (r + 1 + M).choose M := by
      exact_mod_cast hr
    linarith
  rw [hkernel] at hcomparison
  let T := Real.log s - (r : ℝ) * (4 * Real.log d + Real.log A) - E
  let U := (r + 1 : ℝ) * hypersurfaceArchimedeanError r / (r.factorial : ℝ) ^ (1 / (r : ℝ))
  have hsplit : (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (r : ℝ)) * (T - U) =
      (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (r : ℝ)) * T -
          hypersurfaceArchimedeanError r * (s : ℝ) ^ (1 + 1 / (r : ℝ)) := by
    dsimp [U]
    field_simp
  have hraw : (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (r : ℝ)) * (T - U) ≤
        s * M * Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) * Real.log L := by
    rw [hsplit]
    dsimp [T]
    linarith
  have hquot := div_le_div_of_nonneg_right hraw (mul_nonneg hM0.le hs0.le)
  convert hquot using 1
  · rw [Real.rpow_add hs0, Real.rpow_one]
    grind
  · field_simp

/-- A dimension-only error for the normalized, height-controlled inequality. -/
def hypersurfaceNormalizedError (n : ℕ) : ℝ :=
  hypersurfaceHeightDeterminantError n +
    (n + 2 : ℝ) * hypersurfaceArchimedeanError (n + 1) /
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ))
