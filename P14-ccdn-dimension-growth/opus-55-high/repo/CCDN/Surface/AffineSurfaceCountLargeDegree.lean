/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Height.Box
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Surface.DegreeOneCount
import CCDN.Surface.TopFormSurfaceNonlinear

/-! The corrected large-degree surface bound. The auxiliary section's
nonlinear curves and its degree-one components together account
for every bounded integer zero of the original surface. -/

namespace CCDN
section
open MvPolynomial

/-- The degree threshold of the large-degree surface bound `affine_surface_count_large_degree`. It
comes from `surface_inverse_sqrt_le_quarter`: `1 / √d ≤ 1 / 4` once `16 ≤ d`. -/
def topFormSurfaceThreshold : ℕ := 16

