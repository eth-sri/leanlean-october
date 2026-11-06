/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Hilbert.FilteredIntersection
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Algebraic.Defs
import CCDN.Determinant.PlaneSingularities
import CCDN.Projection.CurveDerivativeReconstruction
import CCDN.Projection.ExceptionalCount
import CCDN.Projection.PlaneProjectionDerivative

/-! A degree-preserving linear plane projection of a prime affine curve in
characteristic zero loses at most d(d-1) points from any finite source set.
The proof constructs a common derivative denominator and all reconstruction
identities, with no normalization or exceptional-fiber hypothesis. -/

