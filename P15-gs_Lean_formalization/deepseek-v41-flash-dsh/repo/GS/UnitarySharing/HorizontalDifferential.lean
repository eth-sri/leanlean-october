module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
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
public import GS.GlobalGeometry.ExactSharing
public import GS.GlobalGeometry.FrobeniusProjection
public import GS.GlobalGeometry.SharedAlgebra
public import GS.LieAction.Action
public import GS.LieAction.BlockGroup
public import GS.LieAction.Nonoverlap
public import GS.ManifoldCompletion.OrbitDifferential
public import GS.OriginalLocalModel
public import GS.OverlapGeometry.FactorChartOpen
public import GS.OverlapGeometry.HorizontalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.Frobenius
public import GS.Unitary.FrobeniusProjection
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
public import GS.UnitaryManifold.KernelCayley
public import GS.UnitaryManifold.MatrixCalculus
public import GS.UnitarySharing.Algebra
public import GS.UnitarySharing.Differential
public import GS.UnitarySharing.Directions
public import GS.UnitarySharing.FactorCharts
public import GS.UnitarySharing.FactorCoordinates
public import GS.UnitarySharing.Factors
public import GS.UnitarySharing.HorizontalModel
public import GS.UnitarySharing.Orbit
public import GS.UnitarySharing.ProjectedSlice


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The full differential image after removing the shared stabilizer

The complement has the same differential image as the complete factor model
at every translated centre.  It therefore represents every matrix direction,
including when shared blocks and cross-layer overlap occur simultaneously.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold GS.UnitaryGeometry
open scoped Topology Manifold
namespace GS.UnitarySharing
variable {n : ℕ} {right left : Pattern n}
local instance horizontalDifferentialNormedSpace (P : CMat n) :
    NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _

theorem orbitParam_fderiv_zero_of_kernel (g : Factors right left) (P : CMat n)
    (v : PairGenerator right left)
    (hv : fderiv ℝ (orbitParam (1 : Factors right left) P) 0 v = 0) :
    fderiv ℝ (orbitParam g P) 0 v = 0 := by
  have hi := (orbitParam_kernel_iff_intertwine P v).mp hv
  rw [orbitParam_fderiv_zero]
  simp only [GS.UnitaryGeometry.tangentParam, Matrix.smul_mul, Matrix.mul_smul]
  have he : (Factor.matrix g.1) * v.1.val * P * (Factor.matrix g.2)ᴴ =
      (Factor.matrix g.1) * P * v.2.val * (Factor.matrix g.2)ᴴ := by
    simpa only [Matrix.mul_assoc] using congrArg
      (fun A : CMat n => (Factor.matrix g.1) * A * (Factor.matrix g.2)ᴴ) hi
  rw [he]
  rw [← add_smul]
  norm_num

theorem horizontalOrbit_hasFDerivAt_zero (P : CMat n)
    (g : Factors right left) :
    HasFDerivAt (fun h : HorizontalModel right left P => orbitParam g P h.val)
      ((fderiv ℝ (orbitParam g P) 0).comp
        (HorizontalModel right left P).subtypeL) 0 := by
  have hh := ((orbitParam_smooth g P).differentiable (by simp) 0).hasFDerivAt
  simpa only [map_zero, Function.comp_def] using
    HasFDerivAt.comp (f := fun h : HorizontalModel right left P => h.val)
      (g := orbitParam g P) 0 hh
      (HorizontalModel right left P).subtypeL.hasFDerivAt

theorem horizontalOrbit_fderiv_zero (P : CMat n)
    (g : Factors right left) (h : HorizontalModel right left P) :
    fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 h =
      fderiv ℝ (orbitParam g P) 0 h.val := by
  rw [(horizontalOrbit_hasFDerivAt_zero P g).fderiv]
  rfl

theorem horizontalOrbit_fderiv_zero_range (P : CMat n)
    (g : Factors right left) (Z : CMat n) :
    (∃ h : HorizontalModel right left P,
      fderiv ℝ (fun h : HorizontalModel right left P => orbitParam g P h.val) 0 h = Z) ↔
      Z ∈ pointDirections right left (g • P) := by
  rw [← orbitParam_fderiv_zero_range g P Z]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h.val, (horizontalOrbit_fderiv_zero P g h).symm.trans hh⟩
  · rintro ⟨v, hv⟩
    let z := (horizontalKernelEquiv right left P).symm v
    have hz : (z.1.val : PairGenerator right left) + z.2.val = v :=
      (horizontalKernelEquiv right left P).apply_symm_apply v
    have hk : fderiv ℝ (orbitParam g P) 0 z.2.val = 0 :=
      orbitParam_fderiv_zero_of_kernel g P z.2.val z.2.property
    refine ⟨z.1, ?_⟩
    rw [horizontalOrbit_fderiv_zero, ← hv, ← hz, map_add, hk, add_zero]

end GS.UnitarySharing
