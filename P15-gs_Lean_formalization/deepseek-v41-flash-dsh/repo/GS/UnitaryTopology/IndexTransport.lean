module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import GS.CompactFibres
public import GS.ComplexAlgebra
public import GS.Continuation.CompactCoverageTools
public import GS.Continuation.ExponentialBasics
public import GS.Continuation.ExponentialChart
public import GS.Continuation.PointedCompactImage
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.OrbitCompact
public import GS.Extensions.OriginalCompact
public import GS.Extensions.OriginalFibres
public import GS.Extensions.OriginalUniform
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Fibres
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.GlobalGeometry.OriginalGImage
public import GS.M4Certificate
public import GS.M4Necessary
public import GS.M4Obstruction
public import GS.Nonmanifold.CircleRetract
public import GS.Nonmanifold.NormalizationEstimates
public import GS.Nonmanifold.OriginalCompactModel
public import GS.Nonmanifold.OriginalModelCoordinates
public import GS.Nonmanifold.RadialCone
public import GS.Nonmanifold.RankOneGeometry
public import GS.Nonmanifold.SkewCoordinates
public import GS.NonmanifoldCompletion.BaseFibreGauges
public import GS.NonmanifoldCompletion.BlockExtraction
public import GS.NonmanifoldCompletion.BlockRealization
public import GS.NonmanifoldCompletion.FactorSpace
public import GS.NonmanifoldCompletion.FullFibreCoverage
public import GS.NonmanifoldCompletion.LocalAngles
public import GS.NonmanifoldCompletion.NeighbourhoodModel
public import GS.NonmanifoldCompletion.OriginalCoordinates
public import GS.NonmanifoldCompletion.OriginalMembership
public import GS.NonmanifoldCompletion.SmallLogarithms
public import GS.NonmanifoldCompletion.SpectralTwo
public import GS.NonmanifoldFinal.EuclideanTransport
public import GS.NonmanifoldObstruction.HomogeneousRetraction
public import GS.NonmanifoldObstruction.OpenGerms
public import GS.NonmanifoldObstruction.ProductSphere
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Specifications
public import GS.ThreeFactor
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support
public import GS.UnitaryLocalModel.OuterFibres
public import GS.UnitaryLocalModel.PauliCoordinates
public import GS.UnitaryLocalModel.RankCone
public import GS.UnitaryNonmanifold.BlockInvariant
public import GS.UnitaryNonmanifold.ScalarBridge
public import GS.UnitaryTopology.QuaternionRetraction


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Column reindexing of the actual three-row rank cone

The maps preserve mathlib's matrix rank and the inherited matrix topology.
They allow a four-column-block Clifford construction to be stated at an
ordinary scalar matrix width.
-/
noncomputable section
open Matrix GS GS.NonmanifoldFinal
namespace GS.UnitaryTopology

variable {κ ν : Type*} [Fintype κ] [Fintype ν]

def rankThreeReindex (e : κ ≃ ν) : RankThreeCone κ ≃ₜ RankThreeCone ν where
  toFun W := ⟨W.val.reindex (Equiv.refl _) e, by
    simpa only [Matrix.rank_reindex] using W.property⟩
  invFun W := ⟨W.val.reindex (Equiv.refl _) e.symm, by
    simpa only [Matrix.rank_reindex] using W.property⟩
  left_inv W := by
    apply Subtype.ext
    ext i j
    simp
  right_inv W := by
    apply Subtype.ext
    ext i j
    simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun W : RankThreeCone κ => W.val i (e.symm j))
    exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun W : RankThreeCone ν => W.val i (e j))
    exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)

@[simp] theorem rankThreeReindex_zero (e : κ ≃ ν) :
    rankThreeReindex e rankThreeZero = rankThreeZero := by
  apply Subtype.ext
  ext i j
  rfl

def productRankThreeReindex (e : ℕ) (f : κ ≃ ν) :
    ((Fin e → ℝ) × RankThreeCone κ) ≃ₜ ((Fin e → ℝ) × RankThreeCone ν) :=
  (Homeomorph.refl _).prodCongr (rankThreeReindex f)

@[simp] theorem productRankThreeReindex_zero (e : ℕ) (f : κ ≃ ν) :
    productRankThreeReindex e f (0,rankThreeZero) = (0,rankThreeZero) := by
  exact Prod.ext rfl (rankThreeReindex_zero f)

end GS.UnitaryTopology
