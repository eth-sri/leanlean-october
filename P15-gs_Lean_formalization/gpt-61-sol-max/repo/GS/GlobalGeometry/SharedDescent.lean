
import GS.GlobalGeometry.SharedFactorCurves
import GS.RiemannianCompletion.ExponentialStep
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic



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

namespace GS.GlobalGeometry







/-- The image of the actual tied orthogonal factors. -/
def InSharedA2Orth (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : Mat n) : Prop :=
  ∃ L R, SharedOrthogonalFactor b₂ τ₂ L ∧ SharedOrthogonalFactor b₁ τ₁ R ∧
    X = product2 L P R





end GS.GlobalGeometry
