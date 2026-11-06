module
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
public import GS.GlobalGeometry.BalancedLift
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
public import GS.SharedGeometry.Gradient
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
# Orthogonal shared block geodesics in the actual matrix orbit

Complete physical blocks may be repeated arbitrarily within each layer.
Under no off-diagonal overlap, the block exponential is smooth in the actual
shared orbit, realizes every genuine initial tangent vector, has constant
physical Frobenius speed, and has zero induced covariant acceleration.

Normal acceleration in the independent family is reused only after proving
that every actual shared tangent is an independent generator direction. No
factor-lifting or tangent-surjectivity premise is supplied by the caller.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry
open GS.SharedGeometry
open scoped Topology Manifold
namespace GS.SharedGeodesics
variable {n : ℕ} (right left : Pattern n) (σ : Equiv.Perm (Fin n))
/-- Both physical factors obey their original sharing pattern at every time.
The second group coordinate is transposed to implement the L P R^T action. -/
def orthogonalExpFactors (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) : Factors right left :=
  (Factor.ofMatrix (gsExpLeft (Factor.matrix g.1) C.val t)
    (gsExpLeft_shared left.size left.label left.positive left.divides _ _
      (Factor.matrix_shared g.1) C.property t),
   Factor.ofMatrix (gsExpRight (Factor.matrix g.2)ᵀ Ω.val t)ᵀ
    (shared_factor_transpose
      (gsExpRight_shared right.size right.label right.positive right.divides _ _
        (shared_factor_transpose (Factor.matrix_shared g.2)) Ω.property t)))

def orthogonalExpCurve (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) :
    MatrixOrbit right left (permMatrix σ) :=
  orbitMapToOrbit right left (permMatrix σ) (orthogonalExpFactors right left g C Ω t)

@[simp] theorem orthogonalExpCurve_val (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) :
    (orthogonalExpCurve right left σ g C Ω t).val =
      gsExpCurve (Factor.matrix g.1) (permMatrix σ) (Factor.matrix g.2)ᵀ C.val Ω.val t := by
  change gsExpLeft _ _ t * permMatrix σ * ((gsExpRight _ _ t)ᵀ)ᵀ = _
  simp only [Matrix.transpose_transpose, gsExpCurve, product2]

def orthogonalExpVelocity (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) : Mat n :=
  gsExpVelocity (Factor.matrix g.1) (permMatrix σ) (Factor.matrix g.2)ᵀ C.val Ω.val t

def orthogonalExpAcceleration (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) : Mat n :=
  gsExpAcceleration (Factor.matrix g.1) (permMatrix σ) (Factor.matrix g.2)ᵀ C.val Ω.val t

theorem orthogonalExpCurve_hasDerivAt (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) :
    HasDerivAt (fun s => (orthogonalExpCurve right left σ g C Ω s).val)
      (orthogonalExpVelocity right left σ g C Ω t) t := by
  simpa only [orthogonalExpCurve_val, orthogonalExpVelocity] using
    gsExpCurve_hasDerivAt (Factor.matrix g.1) (permMatrix σ) (Factor.matrix g.2)ᵀ
      C.val Ω.val (perm_orthogonal σ) t

theorem orthogonalExpVelocity_hasDerivAt (g : Factors right left)
    (C : Generator left) (Ω : Generator right) (t : ℝ) :
    HasDerivAt (orthogonalExpVelocity right left σ g C Ω)
      (orthogonalExpAcceleration right left σ g C Ω t) t :=
  gsExpVelocity_hasDerivAt _ _ _ _ _ (perm_orthogonal σ) t

/-- Sharing only restricts the independent tangent image; it does not alter the
ambient acceleration formula. This proves normality against the FULL shared
manifold tangent image at the current time. -/
theorem orthogonalExpAcceleration_normal
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (g : Factors right left) (C : Generator left) (Ω : Generator right)
    (t : ℝ) (Z : Mat n)
    (hZ : Z ∈ pointDirections right left (orthogonalExpCurve right left σ g C Ω t).val) :
    frobInner (orthogonalExpAcceleration right left σ g C Ω t) Z = 0 := by
  let L := gsExpLeft (Factor.matrix g.1) C.val t
  let R := gsExpRight (Factor.matrix g.2)ᵀ Ω.val t
  have hL := gsExpLeft_shared left.size left.label left.positive left.divides _ _
    (Factor.matrix_shared g.1) C.property t
  have hR := gsExpRight_shared right.size right.label right.positive right.divides _ _
    (shared_factor_transpose (Factor.matrix_shared g.2)) Ω.property t
  have hz : Z ∈ pointDirections right left (product2 L (permMatrix σ) R) := by
    simpa only [orthogonalExpCurve_val, gsExpCurve] using hZ
  obtain ⟨A, hA, B, hB, he⟩ :=
    (sharedDirection_iff_pointDirections (right := right) (left := left)
      (permMatrix σ) L R Z hL hR).mpr hz
  exact gsExpCurve_acceleration_normal right.block left.block σ _ _ _ _
    (GS.ManifoldCompletion.noOverlap_offDiagonalDisjoint σ hno)
    (Factor.matrix_orthogonal g.1) (Factor.matrix_orthogonal g.2).transpose
    C.property.1 Ω.property.1 C.property.2.1 Ω.property.2.1 t Z
    ⟨A, B, hA.1, hA.2.1, hB.1, hB.2.1, he⟩

/-- Expanded physical Frobenius norms already include every repeated copy.
No assertion identifies this with the unweighted norm on unique blocks. -/
theorem orthogonalExpCurve_constant_speed
    (hno : GS.LieAction.NoOffDiagonalOverlap right.block left.block σ)
    (g : Factors right left) (C : Generator left) (Ω : Generator right) (t : ℝ) :
    frobSq (orthogonalExpVelocity right left σ g C Ω t) = frobSq C.val + frobSq Ω.val :=
  gsExpCurve_constant_speed right.block left.block σ _ _ _ _
    (GS.ManifoldCompletion.noOverlap_offDiagonalDisjoint σ hno)
    (Factor.matrix_orthogonal g.1) (Factor.matrix_orthogonal g.2).transpose
    C.property.1 Ω.property.1 C.property.2.1 Ω.property.2.1 t

end GS.SharedGeodesics
