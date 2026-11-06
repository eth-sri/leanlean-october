/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Statements
import CCDN.Curve.ProjectiveCurveCount

/-! CCDN Theorem 2 in every ambient dimension. Degree is the slope of
the homogeneous Hilbert function. The height and count use rational
projective points. All projection and plane-counting inputs are proved; the count with an
explicit constant is `projective_curve_count`, in `CCDN.Curve.ProjectiveCurveCount`. -/

namespace CCDN
section
open MvPolynomial

/-- CCDN (2020), Theorem 2: the bound `ProjectiveCurveBound`. -/
theorem projectiveCurveBound : ProjectiveCurveBound := fun n _ ↦
  ⟨projectiveCurveConstant n, projectiveCurveConstant_pos n, fun I _ _ hd hdegree _ hB ↦
    projective_curve_count I hd hdegree hB⟩

