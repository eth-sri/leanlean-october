/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Statements
import CCDN.Curve.ProjectiveCurveCount

/-! CCDN Theorem 2 in every ambient dimension. Degree is the slope of
the homogeneous Hilbert function. The height and count use rational
projective points. All projection and plane-counting inputs are proved; the count with an
explicit constant is `projective_curve_count`, in `CCDN.Curve.ProjectiveCurveCount`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- CCDN (2020), Theorem 2: the bound `ProjectiveCurveBound`. -/
theorem projectiveCurveBound : ProjectiveCurveBound := by
  intro n _
  refine ⟨projectiveCurveConstant n, projectiveCurveConstant_pos n, ?_⟩
  solve_by_elim [projective_curve_count]

end
end CCDN
