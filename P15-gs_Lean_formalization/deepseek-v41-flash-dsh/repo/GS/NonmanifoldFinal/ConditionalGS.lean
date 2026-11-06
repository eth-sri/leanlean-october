module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
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
public import GS.NonmanifoldFinal.FiniteCoordinates
public import GS.NonmanifoldObstruction.HomogeneousRetraction
public import GS.NonmanifoldObstruction.OpenGerms
public import GS.NonmanifoldObstruction.ProductSphere
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Specifications
public import GS.ThreeFactor


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Exact final GS reduction -- CONDITIONAL, not the finished theorem

The sole additional hypothesis is the old, unchanged, standalone
GS.Specifications.ConeProductNonManifoldGoal. It is not proved in this file.
All GS-specific local coverage, membership, coordinate, and chart transport
steps are supplied by the imported, compiler-checked proof scripts.
This declaration must NEVER be reported as an
unconditional proof of GS.Specifications.NonManifoldGoal.
-/
noncomputable section
open Matrix GS GS.Nonmanifold GS.NonmanifoldCompletion GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

/-- The original cone goal applies to the actual independent GS coordinates. -/
theorem model_not_euclidean_of_cone_goal
    (hCone : GS.Specifications.ConeProductNonManifoldGoal)
    (q : ℕ) (hq : 3 ≤ q) : ¬ EuclideanAt (modelCoordinatesZero q) := by
  intro hModel
  let d := Fintype.card (UpperIndex q)
  let e := Fintype.card (FreeIndex q)
  let S : Set ((Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) :=
    {p | p.2.rank ≤ 1}
  have hzero : ((0,0) : (Fin e → ℝ) × Matrix (Fin 2) (Fin d) ℝ) ∈ S := by
    simp [S]
  let h : ModelCoordinates q ≃ₜ S := (modelToFin q).trans flattenConeProduct
  have hpoint : h (modelCoordinatesZero q) = ⟨(0,0),hzero⟩ := by
    change flattenConeProduct (modelToFin q (modelCoordinatesZero q)) = _
    rw [modelToFin_zero]
    rfl
  have hLocal : EuclideanAt (⟨(0,0),hzero⟩ : S) := by
    rw [← hpoint]
    exact (euclideanAt_homeomorph h (modelCoordinatesZero q)).mp hModel
  exact hCone d e (model_width_ge_three q hq)
    ((euclideanAtSubset_iff S (0,0) hzero).mpr hLocal)

end GS.NonmanifoldFinal
