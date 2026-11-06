module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Diagonal
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
public import Mathlib.Tactic.NormNum
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
public import GS.UnitaryLocalModel.DephasedChart
public import GS.UnitaryLocalModel.DephasedDifferential
public import GS.UnitaryLocalModel.Dephasing
public import GS.UnitaryManifold.Action
public import GS.UnitaryManifold.BlockGroup
public import GS.UnitaryManifold.CayleyAlgebra
public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.CayleyDifferential
public import GS.UnitaryManifold.CayleyModel
public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.Dimension
public import GS.UnitaryManifold.Factors
public import GS.UnitaryManifold.HorizontalModel
public import GS.UnitaryManifold.KernelCayley
public import GS.UnitaryManifold.LocalProduct
public import GS.UnitaryManifold.MatrixCalculus


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The dephased chart has the expected real dimension `(q - 1)^2`. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.UnitaryManifold
namespace GS.UnitaryLocalModel
variable {q : ℕ}

theorem finrank_anchorCoordinates (o : Fin q) :
    Module.finrank ℝ (AnchorCoordinates o) = q + (q-1) := by
  classical
  dsimp only [AnchorCoordinates]
  rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi]
  simp only [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- Rank-nullity applied to the explicitly proved onto constraint derivative. -/
theorem finrank_dephasedModel (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    Module.finrank ℝ (DephasedModel Q o) = (q-1)^2 := by
  have hd := LinearMap.finrank_range_add_finrank_ker
    (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o)
  rw [anchorDerivative_range Q o hQ, finrank_top,
    finrank_anchorCoordinates o, finrank_fullModel q] at hd
  have hq : q - 1 + 1 = q := by have ho := o.isLt; omega
  change Module.finrank ℝ (LinearMap.ker
    (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o)) = (q-1)^2
  nlinarith

end GS.UnitaryLocalModel
