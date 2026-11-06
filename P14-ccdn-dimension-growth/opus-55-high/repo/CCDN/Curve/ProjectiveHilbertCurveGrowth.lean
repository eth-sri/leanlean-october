/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.ProjectiveSection
import CCDN.Height.ProjectiveBox
import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Plane.ProjectivePlaneLinearCount
import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Projection.BoundedDegreeNormalizationFiber
import CCDN.Projection.ProjectiveLinearCountTransfer

/-! The plane curve estimate gives a smaller degree exponent for curves
specified by their filtered Hilbert polynomial. The construction of
the finite birational projection and its integer matrix is internal. -/

namespace CCDN
section
open MvPolynomial

