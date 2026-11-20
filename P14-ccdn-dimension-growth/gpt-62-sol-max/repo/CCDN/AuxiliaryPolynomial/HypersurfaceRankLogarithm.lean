/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CCDN.AuxiliaryPolynomial.HypersurfaceRankProfile

/-! The logarithm of the exact hypersurface rank has the uniform leading
term log(d)+r*log(M), with an explicit error depending only on dimension. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Error in the lower bound for the logarithm of the Hilbert rank. -/
def hypersurfaceRankLogError (r : ℕ) : ℝ :=
  (r : ℝ) * Real.log 2 + Real.log (r.factorial : ℝ)

/-- The rank logarithm loses only a dimension constant once M>=2d. -/
theorem hypersurface_rank_log_lower {r d M : ℕ} (hd : 0 < d) (hM : 2 * d ≤ M) :
    Real.log d + (r : ℝ) * Real.log M - hypersurfaceRankLogError r ≤
      Real.log (hypersurfaceRank (r + 1) d M) := by
  have hdM : d ≤ M := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hdMR : 2 * (d : ℝ) ≤ M := by exact_mod_cast hM
  have hfac : (0 : ℝ) < r.factorial := by positivity
  have hl := (hypersurface_rank_power_bounds (r := r) hdM).1
  have hl' : (d : ℝ) * ((M : ℝ) / 2) ^ r / (r.factorial : ℝ) ≤ hypersurfaceRank (r + 1) d M := by
    apply le_trans _ hl
    apply div_le_div_of_nonneg_right _ hfac.le
    apply mul_le_mul_of_nonneg_left _ hd0.le
    exact pow_le_pow_left₀ (by positivity) (by linarith) r
  have hlow :=
    Real.log_le_log (by positivity : (0 : ℝ) < (d : ℝ) * ((M : ℝ) / 2) ^ r / r.factorial) hl'
  rw [Real.log_div (by positivity) hfac.ne', Real.log_mul hd0.ne' (by positivity),
    Real.log_pow, Real.log_div hM0.ne' (by norm_num)] at hlow
  unfold hypersurfaceRankLogError
  linarith

end
end CCDN
