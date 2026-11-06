module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.Core
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Extensions.TwoFactorProjection
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.Projection


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A point-only, globally smooth extension of the m=2 projector

For X = B2 P B1, define
  L_X Z = blockSkew_2 (Z X^T) X,
  R_X Z = X blockSkew_1 (X^T Z),
  Pi_X Z = L_X Z + R_X Z - L_X (R_X Z).

In factor coordinates, L_X and R_X are commuting supported-skew projections.
Thus Pi equals the existing union-mask projector, including overlap. This yields
smoothness in the actual base matrix X, not only smoothness in a chosen pair of
factors. It does NOT establish that the orbit is an embedded manifold, nor does
it assert that Pi_X is a projector for arbitrary nonorthogonal ambient X.

No parameter sharing is imposed. Arbitrary sharing+overlap is NOT covered.
This point-only formula is an auxiliary derived identity, not a quotation from
the manuscript. All original definitions and theorems remain unchanged.
-/

noncomputable section
open Matrix
namespace GS.Continuation
open GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end Smooth

end GS.Continuation
