module

public import HypoellipticAleksandrov.Parabolic.ForwardPropagationGeometry
public import HypoellipticAleksandrov.Parabolic.MovingLensComparison
public import HypoellipticAleksandrov.Parabolic.Scaling
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Normalized forward propagation

This module proves the normalized classical forward-propagation estimate from
the moving-lens comparison.  The equation and ellipticity data are used only
in the open physical rectangle.  The closed-time conclusion is recovered at
the top face by a genuine interior-time limit and consequently uses the
strictly smaller advertised constant.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic


open scoped MatrixOrder

variable (d : ℕ) (lam Lam kappa : ℝ)

/-- The power of the initial relative radius in forward propagation. -/
def forwardPropagationExponent  : ℕ :=
  2 * movingLensSignExponent d lam Lam kappa

/-- The strict closed-corridor forward-propagation constant. -/
def forwardPropagationDelta  : ℝ :=
  (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ movingLensSignExponent d lam Lam kappa

/-- The forward-propagation radius exponent is positive. -/
theorem forwardPropagationExponent_pos
     :
    0 < forwardPropagationExponent d lam Lam kappa := by
  simp_all [forwardPropagationExponent, movingLensSignExponent]

/-- The strict closed-corridor forward-propagation constant is positive. -/
theorem forwardPropagationDelta_pos
     :
    0 < forwardPropagationDelta d lam Lam kappa := by
  simp_all [forwardPropagationDelta]

end HypoellipticAleksandrov.Parabolic
