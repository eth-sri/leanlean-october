/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Determinant.SingularDeterminantCutoff
import CCDN.Height.IntegerCoefficientHeight
import CCDN.AuxiliaryPolynomial.PlaneBadPrimes

/-! The determinant lower bound, with the bad-prime input given by the
coefficient-controlled witness. The sharp finite-field point estimate is an
explicit hypothesis. -/

namespace CCDN
noncomputable section
open Finset MvPolynomial Real

/-- `degreeFourDeterminantError C` plus the constant part `log 7 + 2 mertensError + 1` of the
bad-prime charge of `exists_plane_bad_prime_set`. -/
def heightDeterminantError (C : ℝ) : ℝ :=
  degreeFourDeterminantError C + Real.log 7 + 2 * mertensError + 1

