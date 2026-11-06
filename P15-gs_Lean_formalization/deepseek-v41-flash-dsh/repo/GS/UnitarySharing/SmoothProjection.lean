module
public import Mathlib.Analysis.Calculus.ContDiff.Basic
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
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
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
public import Mathlib.Topology.Constructions.SumProd
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
public import GS.Extensions.OrbitSlices
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
public import GS.OverlapGeometry.ManifoldSmoothMaps
public import GS.OverlapGeometry.SliceAtlas
public import GS.OverlapGeometry.SmoothMaps
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
public import GS.UnitarySharing.HorizontalDifferential
public import GS.UnitarySharing.HorizontalModel
public import GS.UnitarySharing.LocalProduct
public import GS.UnitarySharing.LocalSections
public import GS.UnitarySharing.Orbit
public import GS.UnitarySharing.OrbitAtlas
public import GS.UnitarySharing.ProjectedSlice
public import GS.UnitarySharing.Projection
public import GS.UnitarySharing.TangentBridge


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Joint smoothness of the exact shared tangent projector

On a local smooth factor section the projector is conjugate to the fixed
Frobenius projector at P.  Equivariance makes these formulas agree.  This
proves smoothness on the whole actual shared orbit without a global smooth
factor choice, an entrywise overlap mask, or a variable-rank pseudoinverse
assumption.  The carrier P is arbitrary.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold Set Filter
open scoped Topology Manifold
namespace GS.UnitarySharing
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance smoothProjectionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance smoothProjectionChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
/-- Matrix form of equivariance with arbitrary shared unitary factors. -/
theorem pointProjection_factor_formula (g : Factors right left) (Z : CMat n) :
    pointProjection right left (g • P) Z =
      Factor.matrix g.1 * pointProjection right left P
        ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2) * (Factor.matrix g.2)ᴴ := by
  have h := pointProjection_equivariant g P (g⁻¹ • Z)
  rw [smul_inv_smul] at h
  have hi : g⁻¹ • Z = (Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2 := by
    change (Factor.matrix g.1)ᴴ * Z * ((Factor.matrix g.2)ᴴ)ᴴ = _
    rw [Matrix.conjTranspose_conjTranspose]
  simpa only [hi, action_apply] using h

/-- An ambient smooth extension valid near the source of a fixed slice. -/
def localProjectionFormula (g : Factors right left) (p : CMat n × CMat n) : CMat n :=
  let q := localFactors right left P g p.1
  Factor.matrix q.1 * pointProjection right left P
    ((Factor.matrix q.1)ᴴ * p.2 * Factor.matrix q.2) * (Factor.matrix q.2)ᴴ

theorem localProjectionFormula_eq (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source)
    (Z : CMat n) :
    localProjectionFormula right left P g (X.val, Z) =
      pointProjection right left X.val Z := by
  have he : localFactors right left P g X.val • P = X.val :=
    congrArg Subtype.val (localFactors_right_inverse right left P g X hX)
  have h := pointProjection_factor_formula right left P
    (localFactors right left P g X.val) Z
  rw [he] at h
  exact h.symm

theorem localProjectionFormula_smooth_at (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source)
    (Z : CMat n) :
    ContDiffAt ℝ ⊤ (localProjectionFormula right left P g) (X.val, Z) := by
  have hL := (localFactors_left_matrix_smooth_at right left P g X hX).comp
    (X.val, Z) contDiffAt_fst
  have hR := (localFactors_right_matrix_smooth_at right left P g X hX).comp
    (X.val, Z) contDiffAt_fst
  have hcore := smooth_mul_at (smooth_mul_at (smooth_conjTranspose_at hL) contDiffAt_snd) hR
  have hproj := (pointProjection right left P).contDiff.contDiffAt.comp (X.val, Z) hcore
  exact smooth_mul_at (smooth_mul_at hL hproj) (smooth_conjTranspose_at hR)

/-- The exact point-only projector is smooth jointly in the orbit point and
ambient vector.  The topology and tangent space are those of the new atlas. -/
theorem pointProjection_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, CMat n)) ⊤ (fun p : MatrixOrbit right left P × CMat n =>
        pointProjection right left p.1.val p.2) := by
  intro p
  let g := preferredFactor P p.1
  have h₀ : p.1 ∈ (translatedOrbitSlice right left P g).source := by
    simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g
  have hinc : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, CMat n × CMat n)) ⊤ (fun q : MatrixOrbit right left P × CMat n =>
        (q.1.val, q.2)) :=
    ((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space contMDiff_snd
  have hs := ContDiffAt.comp_contMDiffAt
    (f := fun q : MatrixOrbit right left P × CMat n => (q.1.val, q.2))
    (g := localProjectionFormula right left P g)
    (localProjectionFormula_smooth_at right left P g p.1 h₀ p.2) (hinc p)
  apply hs.congr_of_eventuallyEq
  have hn : ∀ᶠ q : MatrixOrbit right left P × CMat n in 𝓝 p,
      q.1 ∈ (translatedOrbitSlice right left P g).source :=
    (continuous_fst.continuousAt).eventually
      ((translatedOrbitSlice right left P g).open_source.mem_nhds h₀)
  filter_upwards [hn] with q hq
  exact (localProjectionFormula_eq right left P g q.1 hq q.2).symm

end GS.UnitarySharing
