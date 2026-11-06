module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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
public import GS.Projection
public import GS.RiemannianCompletion.FrobeniusDual
public import GS.SharedGeometry.Algebra
public import GS.SharedGeometry.Directions
public import GS.SharedGeometry.Factors
public import GS.SharedGeometry.Orbit
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A canonical continuous projector on each shared orbit

The projector is a function of the matrix point and ambient vector, not of a
chosen factorization.  It equals the existing exact coupled shared projection
at every valid factor pair.  Joint continuity on the actual matrix orbit is
proved by descent through the open orbit map; no continuous choice of factors
and no smooth shared-orbit atlas is assumed.

These statements concern the actual generator range.  Calling it the full
manifold tangent space still requires the shared-orbit atlas.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry
namespace GS.SharedGeometry
variable {n : ℕ} {right left : Pattern n}

/-- Canonical ambient Frobenius projection at a matrix point. -/
def pointProjection (right left : Pattern n) (X : Mat n) : Mat n →L[ℝ] Mat n :=
  frobProjection (pointDirections right left X)

theorem pointProjection_mem (X Z : Mat n) :
    pointProjection right left X Z ∈ pointDirections right left X :=
  frobProjection_mem _ _

theorem pointProjection_of_mem (X Y : Mat n)
    (hY : Y ∈ pointDirections right left X) : pointProjection right left X Y = Y :=
  frobProjection_of_mem _ _ hY

theorem pointProjection_normal (X Z Y : Mat n)
    (hY : Y ∈ pointDirections right left X) :
    frobInner (Z - pointProjection right left X Z) Y = 0 :=
  frobProjection_normal _ _ _ hY

theorem pointProjection_self_adjoint (X Z Y : Mat n) :
    frobInner (pointProjection right left X Z) Y =
      frobInner Z (pointProjection right left X Y) :=
  frobProjection_self_adjoint _ _ _

@[simp] theorem pointProjection_idempotent (X Z : Mat n) :
    pointProjection right left X (pointProjection right left X Z) =
      pointProjection right left X Z :=
  pointProjection_of_mem X _ (pointProjection_mem X Z)

/-- Equivariance follows from the actual action isometry and the full range,
not an entrywise overlap mask. -/
theorem pointProjection_equivariant (g : Factors right left) (X Z : Mat n) :
    pointProjection right left (g • X) (g • Z) =
      g • pointProjection right left X Z := by
  apply frobProjection_unique_normal (pointDirections right left (g • X)) (g • Z)
  · exact action_mem_pointDirections g X _ (pointProjection_mem X Z)
  · intro Y hY
    have hback : g⁻¹ • Y ∈ pointDirections right left X := by
      simpa only [inv_smul_smul] using
        action_mem_pointDirections g⁻¹ (g • X) Y hY
    have he := action_frobInner g (Z - pointProjection right left X Z) (g⁻¹ • Y)
    rw [show g • (Z - pointProjection right left X Z) =
        g • Z - g • pointProjection right left X Z from
          (actionLinearEquiv g).map_sub _ _, smul_inv_smul] at he
    rw [he]
    exact pointProjection_normal X Z _ hback

end GS.SharedGeometry
