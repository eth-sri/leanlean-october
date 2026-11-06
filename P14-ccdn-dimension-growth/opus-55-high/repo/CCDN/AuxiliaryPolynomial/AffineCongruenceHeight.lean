/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Determinant.HypersurfaceDeterminantRank
import CCDN.Height.CountingHypotheses
import CCDN.Plane.IntegerPlaneLogHeight
import CCDN.AuxiliaryPolynomial.CongruenceBadPrimeCharge
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceAuxiliary
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.Determinant.AffineCongruenceDeterminant

/-! The affine congruence determinant bound with all bad-prime charges
controlled by the equation's coefficient height and congruence modulus. -/

namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The logarithmic bad-prime charge in the affine congruence determinant estimate for a form
of degree `d` in `m` variables with coefficient height at most `H`, where `Q` is the sum of
the logarithms of the congruence primes. -/
def congruenceHeightCharge (m d : ℕ) (H Q : ℝ) : ℝ :=
  Real.log (1 + 27 * (d : ℝ) ^ 4 *
    (hypersurfaceHeightConstant m * (1 + Real.log H / (d : ℝ) ^ 2)) + Q) +
      2 * mertensError + 1
