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
public import Mathlib.LinearAlgebra.Basis.VectorSpace
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
public import GS.UnitaryLocalModel.DephasedDimension
public import GS.UnitaryLocalModel.DephasedNeighborhood
public import GS.UnitaryLocalModel.Dephasing
public import GS.UnitaryLocalModel.ZeroLevelChart
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

/-!
# Standard real coordinates for the dephased unitary chart

The kernel chart is transported by a genuine continuous linear equivalence
to `Fin ((q - 1)^2) → ℝ`. No norm-preserving identification is asserted.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.UnitaryManifold Set
open scoped Topology
namespace GS.UnitaryLocalModel
variable {q : ℕ}

/-- A continuous linear coordinate identification with the computed dimension. -/
def dephasedCoordinateEquiv (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    DephasedModel Q o ≃L[ℝ] (Fin ((q-1)^2) → ℝ) := by
  letI : Module.Free ℝ (DephasedModel Q o) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace ℝ (DephasedModel Q o))
  let b : Module.Basis (Fin ((q-1)^2)) ℝ (DephasedModel Q o) :=
    Module.finBasisOfFinrankEq ℝ (DephasedModel Q o) (finrank_dephasedModel Q o hQ)
  let e : DephasedModel Q o ≃ₗ[ℝ] (Fin ((q-1)^2) → ℝ) := b.equivFun
  exact LinearEquiv.toContinuousLinearEquiv
    (𝕜 := ℝ) (E := DephasedModel Q o) (F := Fin ((q-1)^2) → ℝ) e

def euclideanDephasedDomain (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Set (Fin ((q-1)^2) → ℝ) :=
  (dephasedCoordinateEquiv Q o hQ).symm ⁻¹' dephasedChartDomain Q o hQ

def euclideanDephasedParametrization (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (x : Fin ((q-1)^2) → ℝ) : CMat q :=
  dephasedParametrization Q o hQ ((dephasedCoordinateEquiv Q o hQ).symm x)

def euclideanDephasedCoordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o) : Fin ((q-1)^2) → ℝ :=
  dephasedCoordinateEquiv Q o hQ (dephasedCoordinates Q o hQ A)

theorem euclideanDephasedDomain_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : IsOpen (euclideanDephasedDomain Q o hQ) :=
  (dephasedChartDomain_open Q o hQ).preimage (dephasedCoordinateEquiv Q o hQ).symm.continuous

theorem zero_mem_euclideanDephasedDomain (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    (0 : Fin ((q-1)^2) → ℝ) ∈ euclideanDephasedDomain Q o hQ := by
  change (dephasedCoordinateEquiv Q o hQ).symm 0 ∈ dephasedChartDomain Q o hQ
  simpa using zero_mem_dephasedChartDomain Q o hQ

@[simp] theorem euclideanDephasedParametrization_zero (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : euclideanDephasedParametrization Q o hQ 0 = Q.val := by
  simp [euclideanDephasedParametrization]

theorem euclideanDephasedParametrization_continuousOn (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    ContinuousOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) :=
  (dephasedParametrization_continuousOn Q o hQ).comp
    (dephasedCoordinateEquiv Q o hQ).symm.continuous.continuousOn (fun _ h => h)

theorem euclideanDephasedParametrization_injectiveOn (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    Set.InjOn (euclideanDephasedParametrization Q o hQ) (euclideanDephasedDomain Q o hQ) := by
  intro x hx y hy he
  apply (dephasedCoordinateEquiv Q o hQ).symm.injective
  exact dephasedParametrization_injectiveOn Q o hQ hx hy he

/-- The local homeomorphism in the standard real coordinate space. -/
def euclideanDephasedChartHomeomorph (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    dephasedChartSource Q o hQ ≃ₜ euclideanDephasedDomain Q o hQ :=
  (dephasedChartHomeomorph Q o hQ).trans
    ((dephasedCoordinateEquiv Q o hQ).toHomeomorph.subtype
      (fun x => by simp [euclideanDephasedDomain]))

theorem euclideanDephasedParametrization_coordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    euclideanDephasedParametrization Q o hQ (euclideanDephasedCoordinates Q o hQ A) = A.val.val := by
  simpa [euclideanDephasedParametrization, euclideanDephasedCoordinates] using
    dephasedParametrization_coordinates Q o hQ A hA

end GS.UnitaryLocalModel
