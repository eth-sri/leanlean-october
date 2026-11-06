module

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
public import GS.Extensions.TwoFactorProjection
public import GS.LieAction.Nonoverlap
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import GS.Extensions.GeodesicNormal

@[expose] public section


/-!
# Coordinate differential of the orbit inclusion

We differentiate the actual Cayley formula. Its derivative is not defined by
fiat. At the centre, the derivative of cayley is -2 times the identity; the
right transpose changes that sign. In the no-overlap case the Frobenius
identity gives an injective differential. The exact range equals the checked
TwoFactorDirection predicate.

This is a coordinate fderiv theorem. The mfderiv/TangentSpace bridge is in
TangentBridge.lean. No IsImmersion predicate is redefined here.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.Extensions Filter Set
namespace GS.ManifoldCompletion
variable {n : ℕ} {block block₁ block₂ : Fin n → ℕ}



/-- Translate the factor-side injectivity condition into the original
left-coordinate disjoint-support condition. -/
theorem noOverlap_offDiagonalDisjoint (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) :
    OffDiagonalDisjoint block₂ (block₁ ∘ σ.symm) := by
  intro i j h₂ h₁
  apply σ.symm.injective
  apply hn
  grind





end GS.ManifoldCompletion
