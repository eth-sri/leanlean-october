/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib.Tactic

public import CCDN.Determinant.ProjectiveLocalDeterminant
public import CCDN.Determinant.ProjectiveHypersurfaceReduction
import CCDN.Height.ProjectiveZeroLocus

/-! Projective reduction of primitive integer points, and the affine
coordinate charts determined by their finite-field residue points. -/

@[expose] public section
namespace CCDN

variable {p : ℕ} [Fact p.Prime] (r : ProjectiveResidueSpace 2 p)

/-- A coordinate index at which the chosen representative of a point of `ℙ²(𝔽_p)` is nonzero. -/
noncomputable def projectiveResiduePivot    := hypersurfaceResiduePivot r


/-- Integer lifts of the affine coordinates of a point `r` of `ℙ²(𝔽_p)` in the chart where its pivot
coordinate `projectiveResiduePivot r` is moved to the front and set to `1`. -/
noncomputable def projectiveResidueChartLift   :
    CCDN.IntPoint 2 := hypersurfaceResidueChartLift r


/-- Reduction determines both a unit coordinate and all affine congruences;
these are derived from equality of projective residue points. -/
theorem primitiveProjectiveReduction_chart 
    (z : IntPoint 3) (hz : Finset.univ.gcd z = 1)
    (r : ProjectiveResidueSpace 2 p) (he : primitiveProjectiveReduction z hz = r) :
    IsCoprime ↑p (z (projectiveResiduePivot r)) ∧
      ∀ j : Fin 2, ↑p ∣ z (Equiv.swap 0 (projectiveResiduePivot r) j.succ) -
        projectiveResidueChartLift r j * z (projectiveResiduePivot r) :=
  primitiveProjectiveReduction_hypersurface_chart z hz r he


end CCDN
