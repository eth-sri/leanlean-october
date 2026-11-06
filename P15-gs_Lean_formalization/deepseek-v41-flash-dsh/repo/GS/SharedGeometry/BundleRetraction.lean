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
public import Mathlib.Analysis.InnerProductSpace.ProdL2
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
public import GS.GlobalGeometry.BalancedLift
public import GS.GlobalGeometry.CayleyRetraction
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
public import GS.SharedGeometry.CayleyStep
public import GS.SharedGeometry.Differential
public import GS.SharedGeometry.Directions
public import GS.SharedGeometry.FactorCharts
public import GS.SharedGeometry.FactorCoordinates
public import GS.SharedGeometry.Factors
public import GS.SharedGeometry.GeneratorAction
public import GS.SharedGeometry.Gradient
public import GS.SharedGeometry.HorizontalDifferential
public import GS.SharedGeometry.HorizontalModel
public import GS.SharedGeometry.LocalProduct
public import GS.SharedGeometry.LocalSections
public import GS.SharedGeometry.MinimumNormLift
public import GS.SharedGeometry.Orbit
public import GS.SharedGeometry.OrbitAtlas
public import GS.SharedGeometry.ProjectedSlice
public import GS.SharedGeometry.Projection
public import GS.SharedGeometry.Retraction
public import GS.SharedGeometry.Riemannian
public import GS.SharedGeometry.SmoothLift
public import GS.SharedGeometry.SmoothProjection
public import GS.SharedGeometry.TangentBridge
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A canonical smooth retraction on the whole shared tangent bundle

The base is the actual shared matrix orbit, with its inherited-topology atlas.
The retraction is globally defined on mathlib's entire tangent bundle. It
fixes the zero section and its actual manifold differential on every zero
fibre is the identity. Arbitrary overlap and fixed singular carriers are
allowed. This is the exact Cayley map, not a truncated numerical algorithm.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} (right left : Pattern n) (P : Mat n)
local instance bundleRetractionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance bundleRetractionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance bundleRetractionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- Canonical function on the actual whole tangent bundle. -/
def cayleyRetraction
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P)) :
    MatrixOrbit right left P := cayleyFibreRetraction right left P p.proj p.2

@[simp] theorem cayleyRetraction_val
    (p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P)) :
    (cayleyRetraction right left P p).val =
      sharedCayleyValue right left p.proj.val (tangentAmbient right left P p) 1 := rfl

set_option maxHeartbeats 800000 in
/-- Joint smoothness, including the varying base and all tangent fibres. -/
theorem cayleyRetraction_contMDiff :
    ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent
      (𝓘(ℝ, HorizontalModel right left P)) ⊤ (cayleyRetraction right left P) := by
  have hargs : ContMDiff (𝓘(ℝ, HorizontalModel right left P)).tangent
      (((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, Mat n))).prod (𝓘(ℝ, ℝ))) ⊤
      (fun p : TangentBundle (𝓘(ℝ, HorizontalModel right left P)) (MatrixOrbit right left P) =>
        ((p.proj, tangentAmbient right left P p), (1 : ℝ))) :=
    ((Bundle.contMDiff_proj (TangentSpace (𝓘(ℝ, HorizontalModel right left P)))).prodMk
      (tangentAmbient_contMDiff right left P)).prodMk contMDiff_const
  have ha := (sharedCayleyValue_contMDiff right left P).comp hargs
  apply (sharedOrbit_contMDiff_iff_ambient right left P
    (𝓘(ℝ, HorizontalModel right left P)).tangent (cayleyRetraction right left P)).mpr
  simpa only [cayleyRetraction_val, Function.comp_def] using ha

@[simp] theorem cayleyRetraction_zero_section (X : MatrixOrbit right left P) :
    cayleyRetraction right left P ⟨X, 0⟩ = X := cayleyFibreRetraction_zero right left P X

/-- The genuine manifold derivative of the fibre map, not only a matrix expansion. -/
theorem cayleyRetraction_fibre_mfderiv_zero (X : MatrixOrbit right left P) :
    mfderiv (𝓘(ℝ, HorizontalModel right left P)) (𝓘(ℝ, HorizontalModel right left P))
      (fun v : HorizontalModel right left P => cayleyRetraction right left P ⟨X, v⟩)
      (0 : HorizontalModel right left P) = ContinuousLinearMap.id ℝ (HorizontalModel right left P) :=
  cayleyFibreRetraction_mfderiv_zero right left P X

end GS.SharedGeometry
