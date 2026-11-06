/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.ProjectiveSection
import CCDN.Height.ProjectiveBox
import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Hypersurface.ProjectiveHypersurfaceDimensionGrowth
import CCDN.Projection.ProjectiveLinearCountTransfer

/-! The quantitative counting step for the constructed projection. The
height and finite-fiber losses remain polynomial in the original degree. -/

namespace CCDN
section
open MvPolynomial

variable (m k : ℕ)

/-- The exponent `18 + 3 * m + N + 2 * N * (m + 1)`, with `N = m + k + 2`, of the degree in the
point-count bound obtained by projecting an `(m + 1)`-dimensional variety in `ℙ^(m + k + 1)` to a
hypersurface in `ℙ^(m + 2)`. -/
def projectionDegreeExponent : ℕ :=
  18 + 3 * m + (m + k + 2) + 2 * (m + k + 2) * (m + 1)

