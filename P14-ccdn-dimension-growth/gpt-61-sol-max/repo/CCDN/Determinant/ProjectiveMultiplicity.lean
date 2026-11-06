/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Determinant.ProjectiveHypersurfaceMultiplicity

public import CCDN.Determinant.ProjectivePlaneResidueDeterminant
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Determinant.PlaneMultiplicitySmooth
import CCDN.Determinant.PlaneSingularities

/-! Singular projective residue classes are counted in their selected affine
charts. The correction is polynomial in the degree and does not change the
leading finite-field point-count term. -/

public section
namespace CCDN
open MvPolynomial



variable {p d : ℕ} [Fact p.Prime] (f : CCDN.IntegerPolynomial 3) (hf : f.IsHomogeneous d) (hd : 2 ≤ d) (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))


include hd in
/-- The singular correction does not multiply the leading point-count term. -/
theorem projectivePlaneTotalMultiplicity_le_card_add_correction  (hchar : d < p) :
    projectivePlaneTotalMultiplicity f hf hir.ne_zero ≤
      Fintype.card (ProjectivePlaneResidue f p) + 3 * d ^ 2 * (d - 1) := by
  simpa using projectiveHypersurfaceTotalMultiplicity_le_card_add_correction
    (n := 0) f hf hd hir hchar

end CCDN
