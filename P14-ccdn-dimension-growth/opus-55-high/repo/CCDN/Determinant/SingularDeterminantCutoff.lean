/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Analysis.PrimeCutoff
import CCDN.Determinant.SingularReduction
import CCDN.Determinant.PrimeAggregation
import CCDN.Determinant.SingularDeterminant

/-! Fourth-power cutoff removes the polynomial-in-degree error from the
singular determinant prime sum, retaining an explicit logarithmic cutoff cost. -/

namespace CCDN
noncomputable section
open Finset Real MvPolynomial

/-- For `d⁴ ≤ L < p`, the singular-point correction `d² (d - 1)` is at most `d² √p`. -/
lemma singular_correction_absorb {d p : ℕ} (hd : 0 < d) {L : ℝ}
    (hdL : (d : ℝ) ^ 4 ≤ L) (hpL : L < (p : ℝ)) :
    ((d ^ 2 * (d - 1) : ℕ) : ℝ) ≤ (d : ℝ) ^ 2 * Real.sqrt p := by
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hpow : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 4 := by bound
  have hs := Real.le_sqrt_of_sq_le (hpow.trans (hdL.trans hpL.le))
  have hsub : ((d - 1 : ℕ) : ℝ) ≤ d := by simp_all
  push_cast
  exact mul_le_mul_of_nonneg_left (hsub.trans hs) (sq_nonneg _)

/-- The absolute error of the plane determinant lower bound at the cutoff
`stepanovThreshold d`, for residue constant `C` (`singular_determinant_log_lower_at_rank`):
`log 27` from `log (27 d⁴) = log 27 + 4 log d`, `2 mertensError` from Mertens' estimate,
`2 primeBlockMass (C + 1)` from the point-count error `C d² √p` and the singular correction
`d² (d - 1) ≤ d² √p`, and `2 (log 4 + 4)` from the term `s (log 4 + 4) x` at `x = s`. -/
def degreeFourDeterminantError (C : ℝ) : ℝ :=
  Real.log 27 + 2 * mertensError + 2 * primeBlockMass * (C + 1) + 2 * (Real.log 4 + 4)

