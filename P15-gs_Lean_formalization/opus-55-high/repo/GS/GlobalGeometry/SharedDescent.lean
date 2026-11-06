module

public import GS.GlobalGeometry.SharedFactorCurves
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import GS.GeometryAlgebra
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Matrix
public import GS.Core
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import GS.Continuation.ExponentialCurves
public import GS.Extensions.TwoFactorProjection
public import GS.LieAction.Nonoverlap
public import GS.ManifoldCompletion.OrbitDifferential
public import GS.Frobenius
public import GS.Extensions.TransportedProjection
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section


/-!
# Certified descent with actual tied orthogonal factors

A generator lift of the exact shared projection is selected from its proved
existence.  Its matrix-exponential step preserves the actual physical block
ties for every real time when both block sizes are positive and divide the
matrix dimension.  The negative projected ambient gradient has loss slope
minus its squared Frobenius norm; Armijo steps and finite geometric
backtracking follow from differentiability at the base point.

The selected lift need not be unique.  No efficient solver, independence of
factor representation, shared-image manifold, or optimizer convergence rate
is asserted here.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GS.GlobalGeometry
variable {n : ℕ}




/-- The image of the actual tied orthogonal factors. -/
def InSharedA2Orth (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : Mat n) : Prop :=
  ∃ L R, SharedOrthogonalFactor b₂ τ₂ L ∧ SharedOrthogonalFactor b₁ τ₁ R ∧
    X = product2 L P R



end GS.GlobalGeometry
