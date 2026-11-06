/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.ProjectiveChartIdeal
import CCDN.Projection.DegreePreservingProjectionBox
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.Projection.BoundedDegreePreservingProjection
import CCDN.Projection.ProjectivePlaneProjection

/-! A projective curve with a proper standard chart reduces to a plane
equation of the same degree. Projection loses at most d(d-1) affine points
and at most d further points lie on the omitted hyperplane. -/

namespace CCDN
section
open MvPolynomial

