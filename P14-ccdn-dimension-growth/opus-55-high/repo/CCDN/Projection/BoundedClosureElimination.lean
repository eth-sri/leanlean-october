/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IntegerLinearForms
import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Projection.ProjectiveClosureProjection
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Projection.FixedCoordinateElimination
import CCDN.Projection.HilbertLowDegreeEquation
import CCDN.Projection.IntegralProjectionHilbert
import CCDN.Projection.ProjectiveClosureSpecialization

/-! A bounded elimination step whose affine projection and projective
closure projection are both integral. The latter map fixes X₀. -/

namespace CCDN
section
open MvPolynomial

