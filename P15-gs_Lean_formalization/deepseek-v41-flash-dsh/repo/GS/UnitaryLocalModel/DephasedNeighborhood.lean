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
public import GS.UnitaryLocalModel.ZeroLevelChart
public import GS.UnitaryManifold.Action
public import GS.UnitaryManifold.BlockGroup
public import GS.UnitaryManifold.CayleyAlgebra
public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.CayleyDifferential
public import GS.UnitaryManifold.CayleyModel
public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.Factors
public import GS.UnitaryManifold.HorizontalModel
public import GS.UnitaryManifold.KernelCayley
public import GS.UnitaryManifold.LocalProduct
public import GS.UnitaryManifold.MatrixCalculus


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Open-neighbourhood coverage of the dephased unitary chart

The chart image is an open neighbourhood in the full dephased slice, with
its inherited matrix topology. The inverse is the continuous restriction
of the actual implicit-function chart; no coverage assumption is imposed.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold Set
open scoped Topology
namespace GS.UnitaryLocalModel
variable {q : ℕ}

def dephasedBase (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : DephasedUnitary Q o :=
  ⟨Q, (by simpa [anchorConstraints] using anchorConstraints_zero Q o hQ),
    anchorPositive_self Q.val o hQ⟩

def dephasedChartSource (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Set (DephasedUnitary Q o) :=
  {A | A.val ∈ (unitaryConstraintChart Q o hQ).source}

theorem dephasedChartSource_open (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : IsOpen (dephasedChartSource Q o hQ) :=
  (unitaryConstraintChart Q o hQ).open_source.preimage continuous_subtype_val

theorem base_mem_dephasedChartSource (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    dephasedBase Q o hQ ∈ dephasedChartSource Q o hQ :=
  base_mem_unitaryConstraintChart_source Q o hQ

def dephasedCoordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o) : DephasedModel Q o :=
  (unitaryConstraintChart Q o hQ A.val).2

theorem unitaryConstraintChart_of_dephased (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    unitaryConstraintChart Q o hQ A.val = (0, dephasedCoordinates Q o hQ A) := by
  apply Prod.ext
  · rw [unitaryConstraintChart_fst Q o hQ A.val hA]
    exact A.property.1
  · rfl

theorem dephasedParametrization_coordinates (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (A : DephasedUnitary Q o)
    (hA : A ∈ dephasedChartSource Q o hQ) :
    dephasedParametrization Q o hQ (dephasedCoordinates Q o hQ A) = A.val.val := by
  unfold dephasedParametrization
  rw [← unitaryConstraintChart_of_dephased Q o hQ A hA,
    (unitaryConstraintChart Q o hQ).left_inv hA]

/-- The actual homeomorphism between open subsets of the inherited slice
and the real constraint kernel. -/
def dephasedChartHomeomorph (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) :
    dephasedChartSource Q o hQ ≃ₜ dephasedChartDomain Q o hQ :=
  zeroLevelHomeomorph (unitaryConstraintChart Q o hQ)
    (fun A => anchorImag Q.val o A.val = 0 ∧ AnchorPositive Q.val A.val o)
    (by
      intro A hA
      rw [unitaryConstraintChart_fst Q o hQ A hA]
      have hp := ((unitaryConstraintChart_source_iff Q o hQ A).mp hA).2.2
      simp only [hp, and_true])

end GS.UnitaryLocalModel
