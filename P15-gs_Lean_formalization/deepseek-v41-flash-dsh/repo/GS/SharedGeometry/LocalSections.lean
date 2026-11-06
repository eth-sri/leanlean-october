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
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
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
public import GS.SharedGeometry.HorizontalModel
public import GS.SharedGeometry.LocalProduct
public import GS.SharedGeometry.Orbit
public import GS.SharedGeometry.OrbitAtlas
public import GS.SharedGeometry.ProjectedSlice
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Local smooth sections of the shared orbit map

Each translated slice yields an actual local choice of shared factors.  The
choice is smooth on its stated open neighbourhood and reconstructs every point
there.  No global section and no unique factorization are asserted.  In
particular, ambient-smooth orbit curves now admit local smooth factor lifts.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry GS.CayleyCharts Set Filter
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} (right left : Pattern n) (P : Mat n)

/-- Total extension of a local section; its right-inverse identity is asserted
only on the open source of the translated slice. -/
def localFactors (g : Factors right left) (A : Mat n) : Factors right left :=
  factorLift g ((translatedOrbitSlice right left P g).coordinates A).val

theorem localFactors_orbit (g : Factors right left) (A : Mat n) :
    orbitMapToOrbit right left P (localFactors right left P g A) =
      (translatedOrbitSlice right left P g).parametrization
        ((translatedOrbitSlice right left P g).coordinates A) := by
  apply Subtype.ext
  change orbitParam g P ((translatedOrbitSlice right left P g).coordinates A).val =
    g • orbitParam (1 : Factors right left) P
      ((translatedOrbitSlice right left P g).coordinates A).val
  exact orbitParam_eq_translate g P _

/-- Every nearby matrix in the full shared orbit is reconstructed. -/
theorem localFactors_right_inverse (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    orbitMapToOrbit right left P (localFactors right left P g X.val) = X := by
  rw [localFactors_orbit]
  exact (translatedOrbitSlice right left P g).left_inverse X hX

theorem localFactors_left_matrix_smooth_at (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContDiffAt ℝ ⊤ (fun A : Mat n => Factor.matrix (localFactors right left P g A).1) X.val := by
  have hc := (translatedOrbitSlice right left P g).coordinates_smooth X hX
  have hv := (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp X.val hc
  have hl := contDiffAt_fst.comp X.val hv
  exact (reconstruct_matrix_smooth g.1).contDiffAt.comp X.val hl

theorem localFactors_right_matrix_smooth_at (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source) :
    ContDiffAt ℝ ⊤ (fun A : Mat n => Factor.matrix (localFactors right left P g A).2) X.val := by
  have hc := (translatedOrbitSlice right left P g).coordinates_smooth X hX
  have hv := (HorizontalModel right left P).subtypeL.contDiff.contDiffAt.comp X.val hc
  have hr := contDiffAt_snd.comp X.val hv
  exact (reconstruct_matrix_smooth g.2).contDiffAt.comp X.val hr

end GS.SharedGeometry
