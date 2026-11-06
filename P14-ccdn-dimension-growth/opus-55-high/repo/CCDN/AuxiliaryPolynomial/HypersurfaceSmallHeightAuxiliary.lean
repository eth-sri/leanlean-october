/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeComparison
import CCDN.AuxiliaryPolynomial.HypersurfaceSmallHeightDegree
import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeCoordinates
import CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary

/-! Higher-dimensional auxiliary polynomials in the small-height range, with exact
exponents, for any finite prime set whose normalized comparison holds. The
hypersurface instance retains the original geometric bad-prime factor. -/

namespace CCDN
noncomputable section
open MvPolynomial

/-- The coefficient-sensitive threshold, with a dimension-only constant. -/
def hypersurfaceSmallThreshold (n d : ℕ) (B L A : ℝ) : ℝ :=
  Real.exp (hypersurfaceSmallHeightError (n + 1) (hypersurfaceBadPrimeNormalizedError n)) *
    (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * A *
      B ^ ((n + 2 : ℝ) / ((n + 1 : ℝ) * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) /
        L ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ))))

variable {B : ℝ}
