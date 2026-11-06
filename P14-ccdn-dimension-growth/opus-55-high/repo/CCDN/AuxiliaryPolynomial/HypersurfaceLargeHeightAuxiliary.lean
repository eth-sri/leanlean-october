/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.HypersurfaceLargeHeightDegree
import CCDN.AuxiliaryPolynomial.HypersurfaceNormalizedComparison
import CCDN.AuxiliaryPolynomial.Nonmultiple
import CCDN.AuxiliaryPolynomial.PolynomialMapAuxiliary

/-! Auxiliary polynomials in the large-height range. The degree is
O_{n,T}(d^(4-1/(n+1))); the leading-coefficient positioning cost is explicit. -/

namespace CCDN
noncomputable section
open MvPolynomial

def hypersurfaceLargeThreshold (n d : ℕ) (T : ℝ) : ℝ :=
  Real.exp (hypersurfaceLargeHeightError (n + 1) (hypersurfaceNormalizedError n) T) *
    (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ))

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {B : ℝ}
