module

public import GS.Extensions.TransportedProjection
public import GS.Shared.Base
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section


/-!
# Analytic derivatives, rather than only polynomial Taylor identities

Matrix differentiation is reduced to finite
scalar sums, avoiding the need to silently change the matrix norm instance.
The final AD theorem starts with an actual HasFDerivAt hypothesis for the loss.
-/

