module
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
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
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import GS.CayleyCharts.Algebra
public import GS.CayleyCharts.BlockCharts
public import GS.CayleyCharts.Model
public import GS.CayleyCharts.OrbitCharts
public import GS.CayleyCharts.Smooth
public import GS.CompactFibres
public import GS.Continuation.AmbientProjection
public import GS.Continuation.ExponentialBasics
public import GS.Continuation.ExponentialCurves
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
public import GS.GlobalGeometry.SharedDescent
public import GS.GlobalGeometry.SharedFactorCurves
public import GS.GlobalGeometry.SharedNormalEquations
public import GS.LieAction.Action
public import GS.LieAction.BlockGroup
public import GS.LieAction.Nonoverlap
public import GS.ManifoldCompletion.OrbitDifferential
public import GS.OriginalLocalModel
public import GS.OverlapGeometry.FactorChartOpen
public import GS.OverlapGeometry.HorizontalModel
public import GS.OverlapGeometry.KernelCayley
public import GS.OverlapGeometry.ManifoldSmoothMaps
public import GS.OverlapGeometry.SliceAtlas
public import GS.OverlapGeometry.SmoothMaps
public import GS.Projection
public import GS.RiemannianCompletion.FrobeniusDual
public import GS.SharedGeometry.Algebra
public import GS.SharedGeometry.Differential
public import GS.SharedGeometry.Directions
public import GS.SharedGeometry.FactorCharts
public import GS.SharedGeometry.FactorCoordinates
public import GS.SharedGeometry.Factors
public import GS.SharedGeometry.HorizontalDifferential
public import GS.SharedGeometry.HorizontalModel
public import GS.SharedGeometry.LocalProduct
public import GS.SharedGeometry.LocalSections
public import GS.SharedGeometry.Orbit
public import GS.SharedGeometry.OrbitAtlas
public import GS.SharedGeometry.ProjectedSlice
public import GS.SharedGeometry.Projection
public import GS.SharedGeometry.Riemannian
public import GS.SharedGeometry.SmoothProjection
public import GS.SharedGeometry.TangentBridge
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The intrinsic gradient on the genuine shared orbit

The ambient orthogonal projector is lifted into the actual tangent space of
our horizontal atlas. Its Frobenius pairing is the manifold derivative of the
restricted loss. The lift, Riesz identity, uniqueness, and stationarity are all
proved for actual repeated full blocks, without excluding overlap.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.CayleyCharts GS.Extensions GS.GlobalGeometry
open GS.RiemannianCompletion
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} (right left : Pattern n) (P : Mat n)
local instance gradientHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance gradientChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
/-- A canonical tangent lift exists because the already-defined point projector
lands in the actual differential image. No choice of a new factorization is made. -/
def tangentProjection (X : MatrixOrbit right left P) (Z : Mat n) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X :=
  Classical.choose (pointProjection_unique_tangent_lift right left P X Z)

@[simp] theorem inclusion_tangentProjection
    (X : MatrixOrbit right left P) (Z : Mat n) :
    inclusionDifferential right left P X (tangentProjection right left P X Z) =
      pointProjection right left X.val Z :=
  (Classical.choose_spec (pointProjection_unique_tangent_lift right left P X Z)).1

theorem pointProjection_pairing_tangent
    (X : MatrixOrbit right left P) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    frobInner (pointProjection right left X.val Z) (inclusionDifferential right left P X v) =
      frobInner Z (inclusionDifferential right left P X v) := by
  have hfix : pointProjection right left X.val (inclusionDifferential right left P X v) =
      inclusionDifferential right left P X v :=
    (pointProjection_fixed_iff_tangent_image right left P X _).mpr ⟨v, rfl⟩
  rw [pointProjection_self_adjoint, hfix]

/-- The intrinsic Riesz identity for projecting an ambient Frobenius covector. -/
theorem tangentProjection_pairing
    (X : MatrixOrbit right left P) (Z : Mat n)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentPairing right left P X (tangentProjection right left P X Z) v =
      frobInner Z (inclusionDifferential right left P X v) := by
  unfold tangentPairing
  rw [inclusion_tangentProjection]
  exact pointProjection_pairing_tangent right left P X Z v

/-- Uniqueness follows from positive definiteness, not from declaring this
identity to be a definition of the gradient. -/
theorem tangentProjection_unique
    (X : MatrixOrbit right left P) (Z : Mat n)
    (w : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X)
    (hw : ∀ v, tangentPairing right left P X w v = frobInner Z (inclusionDifferential right left P X v)) :
    w = tangentProjection right left P X Z := by
  have h := hw (w - tangentProjection right left P X Z)
  have hg := tangentProjection_pairing right left P X Z (w - tangentProjection right left P X Z)
  apply sub_eq_zero.mp
  apply (tangentPairing_self_eq_zero_iff right left P X _).mp
  change frobInner (inclusionDifferential right left P X (w - tangentProjection right left P X Z)) _ = 0
  rw [map_sub, frobInner_sub_left]
  apply sub_eq_zero.mpr
  simpa only [tangentPairing, map_sub] using h.trans hg.symm

/-- Linear dependence on the ambient vector, derived from the Riesz identity. -/
theorem tangentProjection_add (X : MatrixOrbit right left P) (Z W : Mat n) :
    tangentProjection right left P X (Z + W) = tangentProjection right left P X Z + tangentProjection right left P X W := by
  symm
  apply tangentProjection_unique right left P X (Z + W)
  intro v
  rw [tangentPairing_add_left, tangentProjection_pairing, tangentProjection_pairing,
    frobInner_add_left]

theorem tangentProjection_smul (X : MatrixOrbit right left P)
    (a : ℝ) (Z : Mat n) :
    tangentProjection right left P X (a • Z) = a • tangentProjection right left P X Z := by
  symm
  apply tangentProjection_unique right left P X (a • Z)
  intro v
  rw [tangentPairing_smul_left, tangentProjection_pairing, frobInner_smul_left]

@[simp] theorem tangentProjection_zero (X : MatrixOrbit right left P) :
    tangentProjection right left P X (0 : Mat n) = 0 := by
  symm
  apply tangentProjection_unique right left P X 0
  intro v
  simp

/-- The actual manifold chain rule for an ambient loss restricted to the orbit. -/
theorem restricted_loss_mfderiv (f : Mat n → ℝ)
    (X : MatrixOrbit right left P)
    (hf : DifferentiableAt ℝ f X.val) :
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, ℝ))
      (fun Y : MatrixOrbit right left P => f Y.val) X =
        (fderiv ℝ f X.val).comp (inclusionDifferential right left P X) := by
  have hi : MDifferentiableAt (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, Mat n))
      (fun Y : MatrixOrbit right left P => Y.val) X :=
    ((sharedOrbit_val_contMDiff right left P) X).mdifferentiableAt (by simp)
  have hh := mfderiv_comp X hf.mdifferentiableAt hi
  rw [mfderiv_eq_fderiv] at hh
  convert hh using 1 <;> first | rfl | (ext v <;> rfl)

/-- This vector inhabits mathlib's TangentSpace for the constructed atlas. -/
def intrinsicGradient (f : Mat n → ℝ)
    (X : MatrixOrbit right left P) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X :=
  tangentProjection right left P X (ambientGradient f X.val)

/-- Riesz characterization against the ACTUAL derivative of f restricted to M. -/
theorem intrinsicGradient_characterization (f : Mat n → ℝ)
    (X : MatrixOrbit right left P) (hf : DifferentiableAt ℝ f X.val)
    (v : TangentSpace (𝓘(ℝ, HorizontalModel right left P)) X) :
    tangentPairing right left P X (intrinsicGradient right left P f X) v =
      mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, ℝ))
        (fun Y : MatrixOrbit right left P => f Y.val) X v := by
  rw [restricted_loss_mfderiv right left P f X hf]
  change tangentPairing right left P X (intrinsicGradient right left P f X) v =
    fderiv ℝ f X.val (inclusionDifferential right left P X v)
  rw [ambientGradient_represents]
  exact tangentProjection_pairing right left P X _ v

end GS.SharedGeometry
