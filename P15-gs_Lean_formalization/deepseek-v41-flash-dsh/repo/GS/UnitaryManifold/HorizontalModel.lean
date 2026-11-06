module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Order.Compact
public import GS.CayleyCharts.Algebra
public import GS.CayleyCharts.BlockCharts
public import GS.CayleyCharts.Model
public import GS.CayleyCharts.OrbitCharts
public import GS.CayleyCharts.Smooth
public import GS.CompactFibres
public import GS.ComplexAlgebra
public import GS.Continuation.AmbientProjection
public import GS.Core
public import GS.Extensions.GeodesicNormal
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Extensions.TwoFactorProjection
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.LieAction.Action
public import GS.LieAction.BlockGroup
public import GS.LieAction.Nonoverlap
public import GS.ManifoldCompletion.OrbitDifferential
public import GS.OverlapGeometry.HorizontalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.Frobenius
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.Projection
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support
public import GS.UnitaryManifold.Action
public import GS.UnitaryManifold.BlockGroup
public import GS.UnitaryManifold.CayleyAlgebra
public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.CayleyDifferential
public import GS.UnitaryManifold.CayleyModel
public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.Factors
public import GS.UnitaryManifold.MatrixCalculus


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A horizontal complement for the orbit differential

All finite-dimensional choices in this file are constructed from complements
of submodules. The horizontal restriction is injective and has a continuous
linear left inverse defined on the full ambient matrix space. No hypothesis
excluding overlap is used.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.UnitaryGeometry GS.OverlapGeometry

namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000

variable {n : ℕ}

/-- The actual differential of the original factor parametrization. -/
def orbitDerivative (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    PairModel b₁ b₂ →L[ℝ] CMat n :=
  fderiv ℝ (orbitParam (1 : FactorGroup b₁ b₂) (cPermMatrix σ)) 0

abbrev OrbitKernel (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :=
  LinearMap.ker (orbitDerivative b₁ b₂ σ).toLinearMap

abbrev HorizontalModel (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    Submodule ℝ (PairModel b₁ b₂) :=
  horizontalComplement (orbitDerivative b₁ b₂ σ)

end GS.UnitaryManifold
