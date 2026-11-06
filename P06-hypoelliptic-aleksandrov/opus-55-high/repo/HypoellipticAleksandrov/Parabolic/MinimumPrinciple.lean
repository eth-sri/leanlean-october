module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.Parabolic.Operator

/-!
# Pointwise parabolic minimum principle

This module proves the one-sided pointwise calculus statement behind the classical
forward parabolic minimum principle. At a local minimum relative to all earlier times,
the time derivative is nonpositive and the velocity Hessian is positive semidefinite.
Consequently, a positive semidefinite coefficient matrix gives the expected sign for
the forward parabolic operator.

The regularity assumption is pointwise `ContDiffAt ℝ 2 u z`. The second-derivative
argument is localized along affine lines through `z`; no global smoothness assumption
or comparison principle is used.

## Main results

* `velocityHessian_posSemidef_of_past_localMin`: positivity of the velocity Hessian.
* `timeDerivative_nonpos_of_past_localMin`: the one-sided time-derivative sign.
* `parabolicOperator_nonpos_of_past_localMin`: the pointwise operator sign.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology

end HypoellipticAleksandrov.Parabolic
