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
public import Mathlib.Analysis.InnerProductSpace.ProdL2
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
public import GS.UnitarySharing.GeneratorAction
public import GS.UnitarySharing.HorizontalModel
public import GS.UnitarySharing.LocalProduct
public import GS.UnitarySharing.LocalSections
public import GS.UnitarySharing.MinimumNormLift
public import GS.UnitarySharing.Orbit
public import GS.UnitarySharing.OrbitAtlas
public import GS.UnitarySharing.ProjectedSlice
public import GS.UnitarySharing.Projection


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth minimum-physical-norm lifting on a fixed shared orbit

At a point g.P the canonical lift is Ad(g) D_P^dagger (g^-1.Z).
A smooth local factor section gives a smooth formula; equivariance makes
all such local formulas agree. The carrier may be singular, even zero.
No smooth pseudoinverse across changing orbit ranks is assumed.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryManifold Set Filter
open scoped Topology Manifold
namespace GS.UnitarySharing
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance smoothLiftNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance smoothLiftChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
/-- Polynomial transport of a fixed linear lift. The model projections only
provide total extensions off the shared factor group. -/
def transportedMinimumNormLift (p : CMat n × (CMat n × CMat n)) : PairGenerator right left :=
  let v := minimumNormLift right left P (p.1ᴴ * p.2.2 * p.2.1)
  (modelProjection left (p.1 * v.1.val * p.1ᴴ),
   modelProjection right (p.2.1 * v.2.val * p.2.1ᴴ))

theorem transportedMinimumNormLift_smooth :
    ContDiff ℝ ⊤ (transportedMinimumNormLift right left P) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hL : ContDiffAt ℝ ⊤ (fun q : CMat n × (CMat n × CMat n) => q.1) p := contDiffAt_fst
  have hR : ContDiffAt ℝ ⊤ (fun q : CMat n × (CMat n × CMat n) => q.2.1) p := contDiffAt_snd.fst
  have hZ : ContDiffAt ℝ ⊤ (fun q : CMat n × (CMat n × CMat n) => q.2.2) p := contDiffAt_snd.snd
  have hv := (minimumNormLift right left P).contDiff.contDiffAt.comp p
    (smooth_mul_at (smooth_mul_at (smooth_conjTranspose_at hL) hZ) hR)
  have hvL := (GS.UnitarySharing.sharedSkewSpace (n := n) left.size left.label).subtypeL.contDiff.contDiffAt.comp p hv.fst
  have hvR := (GS.UnitarySharing.sharedSkewSpace (n := n) right.size right.label).subtypeL.contDiff.contDiffAt.comp p hv.snd
  exact ((modelProjection left).contDiff.contDiffAt.comp p
    (smooth_mul_at (smooth_mul_at hL hvL) (smooth_conjTranspose_at hL))).prodMk
    ((modelProjection right).contDiff.contDiffAt.comp p
      (smooth_mul_at (smooth_mul_at hR hvR) (smooth_conjTranspose_at hR)))

theorem transportedMinimumNormLift_on_factors (g : Factors right left) (Z : CMat n) :
    transportedMinimumNormLift right left P (Factor.matrix g.1, (Factor.matrix g.2, Z)) =
      minimumNormLift right left (g • P) Z := by
  rw [minimumNormLift_factor_formula]
  have he : g⁻¹ • Z = (Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2 := by
    change (Factor.matrix g.1)ᴴ * Z * ((Factor.matrix g.2)ᴴ)ᴴ = _
    rw [Matrix.conjTranspose_conjTranspose]
  rw [he]
  apply Prod.ext
  · exact modelProjection_inclusion (generatorAction g
      (minimumNormLift right left P ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2))).1
  · exact modelProjection_inclusion (generatorAction g
      (minimumNormLift right left P ((Factor.matrix g.1)ᴴ * Z * Factor.matrix g.2))).2

/-- A fixed local section produces an ambient extension near its source. -/
def localMinimumNormLift (g : Factors right left) (p : CMat n × CMat n) : PairGenerator right left :=
  let q := localFactors right left P g p.1
  transportedMinimumNormLift right left P (Factor.matrix q.1, (Factor.matrix q.2, p.2))

theorem localMinimumNormLift_eq (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source)
    (Z : CMat n) :
    localMinimumNormLift right left P g (X.val, Z) = minimumNormLift right left X.val Z := by
  have he : localFactors right left P g X.val • P = X.val :=
    congrArg Subtype.val (localFactors_right_inverse right left P g X hX)
  change transportedMinimumNormLift right left P _ = _
  rw [transportedMinimumNormLift_on_factors, he]

theorem localMinimumNormLift_smooth_at (g : Factors right left)
    (X : MatrixOrbit right left P) (hX : X ∈ (translatedOrbitSlice right left P g).source)
    (Z : CMat n) :
    ContDiffAt ℝ ⊤ (localMinimumNormLift right left P g) (X.val, Z) := by
  have hL := (localFactors_left_matrix_smooth_at right left P g X hX).comp
    (X.val, Z) contDiffAt_fst
  have hR := (localFactors_right_matrix_smooth_at right left P g X hX).comp
    (X.val, Z) contDiffAt_fst
  exact (transportedMinimumNormLift_smooth right left P).contDiffAt.comp
    (X.val, Z) (hL.prodMk (hR.prodMk contDiffAt_snd))

/-- Joint smoothness on the whole fixed orbit times the ambient matrix space. -/
theorem minimumNormLift_contMDiff :
    ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, PairGenerator right left)) ⊤
      (fun p : MatrixOrbit right left P × CMat n => minimumNormLift right left p.1.val p.2) := by
  intro p
  let g := preferredFactor P p.1
  have h₀ : p.1 ∈ (translatedOrbitSlice right left P g).source := by
    simpa only [g, preferredFactor_spec] using translatedOrbitSlice_centre_mem right left P g
  have hinc : ContMDiff ((𝓘(ℝ, HorizontalModel right left P)).prod (𝓘(ℝ, CMat n)))
      (𝓘(ℝ, CMat n × CMat n)) ⊤ (fun q : MatrixOrbit right left P × CMat n => (q.1.val, q.2)) :=
    ((sharedOrbit_val_contMDiff right left P).comp contMDiff_fst).prodMk_space contMDiff_snd
  have hs := ContDiffAt.comp_contMDiffAt
    (f := fun q : MatrixOrbit right left P × CMat n => (q.1.val, q.2))
    (g := localMinimumNormLift right left P g)
    (localMinimumNormLift_smooth_at right left P g p.1 h₀ p.2) (hinc p)
  apply hs.congr_of_eventuallyEq
  have hn : ∀ᶠ q : MatrixOrbit right left P × CMat n in 𝓝 p,
      q.1 ∈ (translatedOrbitSlice right left P g).source :=
    (continuous_fst.continuousAt).eventually
      ((translatedOrbitSlice right left P g).open_source.mem_nhds h₀)
  filter_upwards [hn] with q hq
  exact (localMinimumNormLift_eq right left P g q.1 hq q.2).symm

end GS.UnitarySharing
