/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfaceRankArchimedean

/-! The normalized higher-dimensional determinant inequality, retaining the
exact root-rank and kernel-rank coefficients needed for uniform degree selection. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Absorb the archimedean rank terms and divide by Ms. No fixed-factor
approximation of the leading rank or coefficient-height term is made. -/
theorem hypersurface_rank_comparison_normalized {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hdM : d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M)
    (B L A E : ℝ)
    (hcomparison : (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (r : ℝ)) *
          (Real.log s - (r : ℝ) * (4 * Real.log d + Real.log A) - E) ≤
      Real.log (s.factorial : ℝ) +
        s * M * Real.log B - (((r + 1 + M).choose M : ℝ) - s) * Real.log L) :
    (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) / ((r + 1 : ℝ) * M) *
      (Real.log s - (r : ℝ) * (4 * Real.log d + Real.log A) -
        (E + (r + 1 : ℝ) * (r : ℝ) / (r.factorial : ℝ) ^ (1 / (r : ℝ)))) ≤
      Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) * Real.log L := by
  have hMs := hypersurface_rank_ge_degree_parameter hrpos hd hdM hr
  have hs0 : (0 : ℝ) < s := by bound
  have hM0 : (0 : ℝ) < M := by bound
  have hr1 : (r + 1 : ℝ) ≠ 0 := by positivity
  have hfac : (r.factorial : ℝ) ^ (1 / (r : ℝ)) ≠ 0 := by positivity
  have harch := log_factorial_rank_le hrpos ((hd.trans_le hdM).trans_le hMs)
  have hkernel : ((r + 1 + M).choose M : ℝ) - s = (r + 1 + (M - d)).choose (M - d) := by
    have hh : (s : ℝ) + ((r + 1 + (M - d)).choose (M - d) : ℝ) = (r + 1 + M).choose M := by
      exact_mod_cast hr
    linarith
  rw [hkernel] at hcomparison
  let T := Real.log s - r * (4 * Real.log d + Real.log A) - E
  let U := (r + 1) * (r : ℝ) / r.factorial ^ (1 / (r : ℝ))
  have hsplit : (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (r : ℝ)) * (T - U) =
      (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (r : ℝ)) * T -
          (r : ℝ) * (s : ℝ) ^ (1 + 1 / (r : ℝ)) := by
    grind
  have hraw : (r.factorial : ℝ) ^ (1 / (r : ℝ)) / (r + 1 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (r : ℝ)) * (T - U) ≤
        s * M * Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) * Real.log L := by
    grind
  have hquot := div_le_div_of_nonneg_right hraw (mul_nonneg hM0.le hs0.le)
  convert hquot using 1
  grind [Real.rpow_add, Real.rpow_one]
  · field_simp

end
end CCDN
