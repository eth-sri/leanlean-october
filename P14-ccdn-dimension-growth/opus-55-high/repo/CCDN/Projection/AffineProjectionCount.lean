/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Hilbert.AffineCurveDegree
import CCDN.Projection.DegreePreservingProjectionBox
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Determinant.PolynomialMapDeterminant
import CCDN.Projection.BoundedDegreePreservingProjection

/-! Reduce the integral-point count of an arbitrary prime affine curve
to the proved plane count, using the constructed degree-preserving projection. -/

namespace CCDN
section
open MvPolynomial

/-- The inclusion of integer points into rational points is injective. -/
lemma rationalPoint_injective (n : ℕ) : Function.Injective (@rationalPoint n) := by
  intro z w he
  funext j
  have hh := congrFun he j
  change (z j : ℚ) = (w j : ℚ) at hh
  exact_mod_cast hh

