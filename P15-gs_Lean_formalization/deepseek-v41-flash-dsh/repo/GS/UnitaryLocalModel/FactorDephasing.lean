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
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
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
public import Mathlib.Topology.Instances.Real.Lemmas
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
public import GS.Continuation.ExponentialBasics
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.GeodesicNormal
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.OriginalCompact
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Extensions.TwoFactorProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.LieAction.Action
public import GS.LieAction.BlockGroup
public import GS.LieAction.Nonoverlap
public import GS.ManifoldCompletion.OrbitDifferential
public import GS.NonmanifoldCompletion.BlockRealization
public import GS.NonmanifoldCompletion.SpectralTwo
public import GS.OriginalLocalModel
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
public import GS.UnitaryLocalModel.DephasedNeighborhood
public import GS.UnitaryLocalModel.Dephasing
public import GS.UnitaryLocalModel.DephasingTopology
public import GS.UnitaryLocalModel.FactorSpace
public import GS.UnitaryLocalModel.NormalizationAlgebra
public import GS.UnitaryLocalModel.NormalizationBaseFibre
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
public import GS.UnitaryNonmanifold.BlockInvariant
public import GS.UnitaryNonmanifold.ScalarBridge


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Continuous dephased cores on the full compact factor space

The nonzero-anchor condition cuts out an open subset of the full factor
space. Both normalized middle factors are continuous maps into the genuine
dephased unitary slice, with its inherited matrix topology.
-/

noncomputable section
open Matrix GS GS.UnitaryNonmanifold
namespace GS.UnitaryLocalModel
variable {q : ℕ}

def anchorFactorSet (Q : FullUnitary q) (o : Fin q) : Set (SmallFactorSpace q) :=
  {p | AnchorNonzero Q.val p.val.2.1 o ∧ AnchorNonzero Q.val p.val.2.2.1 o}

theorem anchorFactorSet_open (Q : FullUnitary q) (o : Fin q) :
    IsOpen (anchorFactorSet Q o) := by
  exact ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop)).inter
    ((isOpen_anchorNonzero Q.val o).preimage (by fun_prop))

def dephasedFirst (Q : FullUnitary q) (o : Fin q)
    (p : anchorFactorSet Q o) : DephasedUnitary Q o :=
  ⟨fullUnitary (dephase Q.val p.val.val.2.1 o)
      (dephase_unitary p.val.property.2.1 p.property.1),
    (dephased_constraints_iff _ _ _).mpr
      ⟨dephase_anchor_column_positive p.property.1,
        dephase_anchor_row_positive p.property.1⟩⟩

def dephasedSecond (Q : FullUnitary q) (o : Fin q)
    (p : anchorFactorSet Q o) : DephasedUnitary Q o :=
  ⟨fullUnitary (dephase Q.val p.val.val.2.2.1 o)
      (dephase_unitary p.val.property.2.2.1 p.property.2),
    (dephased_constraints_iff _ _ _).mpr
      ⟨dephase_anchor_column_positive p.property.2,
        dephase_anchor_row_positive p.property.2⟩⟩

theorem continuous_dephasedFirst (Q : FullUnitary q) (o : Fin q) :
    Continuous (dephasedFirst Q o) := by
  have hc : Continuous (fun p : anchorFactorSet Q o => dephase Q.val p.val.val.2.1 o) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := fun p : anchorFactorSet Q o => p.val.val.2.1)
      (continuousAt_dephase p.property.1) (by fun_prop)
  exact (hc.subtype_mk _).subtype_mk _

theorem continuous_dephasedSecond (Q : FullUnitary q) (o : Fin q) :
    Continuous (dephasedSecond Q o) := by
  have hc : Continuous (fun p : anchorFactorSet Q o => dephase Q.val p.val.val.2.2.1 o) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := fun p : anchorFactorSet Q o => p.val.val.2.2.1)
      (continuousAt_dephase p.property.2) (by fun_prop)
  exact (hc.subtype_mk _).subtype_mk _

/-- Every representative of the scalar base fibre satisfies the anchor condition. -/
theorem base_fibre_mem_anchorFactorSet (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (p : SmallFactorSpace q)
    (he : ∀ i j, p.val.1 i * diagTwo (p.val.2.1 i j) (p.val.2.2.1 i j) *
      p.val.2.2.2 j = Q.val i j • (1 : CMat 2)) : p ∈ anchorFactorSet Q o :=
  base_fibre_anchor_nonzero p.val.1 p.val.2.2.2 Q.val p.val.2.1 p.val.2.2.1 o
    p.property.1 p.property.2.2.2 (fun i => (hQ.1 i).1) (fun j => (hQ.2 j).1) he

theorem dephasedFirst_eq_base (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (p : anchorFactorSet Q o)
    (he : ∀ i j, p.val.val.1 i * diagTwo (p.val.val.2.1 i j) (p.val.val.2.2.1 i j) *
      p.val.val.2.2.2 j = Q.val i j • (1 : CMat 2)) :
    dephasedFirst Q o p = dephasedBase Q o hQ := by
  apply Subtype.ext
  apply Subtype.ext
  exact (base_fibre_dephased_middle p.val.val.1 p.val.val.2.2.2 Q.val
    p.val.val.2.1 p.val.val.2.2.1 o p.val.property.1 p.val.property.2.2.2
    (fun i => (hQ.1 i).1) (fun j => (hQ.2 j).1) he).1

theorem dephasedSecond_eq_base (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (p : anchorFactorSet Q o)
    (he : ∀ i j, p.val.val.1 i * diagTwo (p.val.val.2.1 i j) (p.val.val.2.2.1 i j) *
      p.val.val.2.2.2 j = Q.val i j • (1 : CMat 2)) :
    dephasedSecond Q o p = dephasedBase Q o hQ := by
  apply Subtype.ext
  apply Subtype.ext
  exact (base_fibre_dephased_middle p.val.val.1 p.val.val.2.2.2 Q.val
    p.val.val.2.1 p.val.val.2.2.1 o p.val.property.1 p.val.property.2.2.2
    (fun i => (hQ.1 i).1) (fun j => (hQ.2 j).1) he).2

end GS.UnitaryLocalModel
