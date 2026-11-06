/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.HypersurfaceRankLogarithm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.AuxiliaryPolynomial.HypersurfaceKernelRatio
import CCDN.AuxiliaryPolynomial.HypersurfaceRankRoots
import CCDN.AuxiliaryPolynomial.RatioEstimates
import CCDN.ForMathlib.Log

/-! The small-height numerical auxiliary-degree bound, with exact box and
coefficient exponents and a constant depending only on dimension. -/

namespace CCDN
noncomputable section

/-- The additive error term, depending only on the dimension `r` and the constant `E`, in the
small-height logarithmic bound on the auxiliary degree `M`. -/
def hypersurfaceSmallHeightError (r : ℕ) (E : ℝ) : ℝ :=
  (E + hypersurfaceRankLogError r + 4 * (r + 1 : ℝ) ^ 2) / r

/-- Solve the normalized exact-rank inequality in the small-height range. -/
theorem hypersurface_small_height_log_degree_bound {r d M s : ℕ}
    (hrpos : 0 < r) (hd : 0 < d) (hM : 2 * d ≤ M)
    (hr : s + (r + 1 + (M - d)).choose (M - d) = (r + 1 + M).choose M)
    (B L A E : ℝ) (hB : 1 ≤ B) (hL : 1 ≤ L) (hA : 0 < A)
    (hheight : Real.log L ≤ 2 * d * (r + 1 : ℝ) * Real.log B)
    (hscale : (d : ℝ) * Real.log B ≤ (d : ℝ) ^ (1 / (r : ℝ)) * M)
    (hcomparison : (r.factorial : ℝ) ^ (1 / (r : ℝ)) * (s : ℝ) ^ (1 / (r : ℝ)) /
        ((r + 1 : ℝ) * M) *
        (Real.log s - (r : ℝ) * (4 * Real.log d + Real.log A) - E) ≤
      Real.log B - ((r + 1 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) * Real.log L) :
    (M : ℝ) ≤ Real.exp (hypersurfaceSmallHeightError r E) * (d : ℝ) ^ (4 - 1 / (r : ℝ)) * A *
      B ^ ((r + 1 : ℝ) / ((r : ℝ) * (d : ℝ) ^ (1 / (r : ℝ)))) /
        L ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) := by
  have hdM : d ≤ M := by omega
  have hL0 : 0 < L := by linarith
  refine Real.natCast_le_of_log_le_log (by omega) (by positivity) ?_
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hA.ne',
    Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
    Real.log_rpow (mod_cast hd), Real.log_rpow (by linarith), Real.log_rpow hL0]
  have hr0 : (0 : ℝ) < r := mod_cast hrpos
  have hM0 : (0 : ℝ) < M := by bound
  have hX : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  obtain ⟨halow, haup⟩ := hypersurface_rank_root_bounds hrpos hdM hr
  have hk := (hypersurface_kernel_ratio_bounds hd hdM hr).1
  have hh := auxiliary_small_height_bracket_bound (r := r) (Nat.cast_nonneg r)
    (mod_cast hd) (mod_cast hM) hX halow haup (by positivity) hk
    (Real.log_nonneg hB) (Real.log_nonneg hL) hheight hscale hcomparison
  have hlog := (abs_le.mp (hypersurface_rank_log_error hrpos hd hM hr)).1
  have hraw : (r : ℝ) * Real.log M ≤ (r + 1 : ℝ) / (d : ℝ) ^ (1 / (r : ℝ)) * Real.log B -
      Real.log L / ((d : ℝ) * (d : ℝ) ^ (1 / (r : ℝ))) +
      4 * (r + 1 : ℝ) ^ 2 + E + hypersurfaceRankLogError r +
      (4 * (r : ℝ) - 1) * Real.log d + r * Real.log A := by
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hraw hr0.le
  rw [mul_div_cancel_left₀ (Real.log M) hr0.ne'] at hdiv
  convert hdiv using 1
  unfold hypersurfaceSmallHeightError
  field_simp
  ring

