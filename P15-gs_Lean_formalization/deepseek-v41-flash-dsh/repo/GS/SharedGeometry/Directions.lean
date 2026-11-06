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
public import GS.SharedGeometry.Factors
public import GS.SharedGeometry.Orbit
public import GS.Shuffle


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Factor-independent infinitesimal directions for shared layers

The point map (A,B) |-> A X + X B is defined directly from X.  Conjugation
closure of the tied generator spaces identifies its range with the old
factor-coordinate formula for every valid factorization.  Thus the range
and the set of realized tied-factor velocities do not depend on that choice.

`pointDirections` is deliberately not called a tangent bundle.  The full
shared-orbit atlas and identification with its manifold differential remain
separate tasks.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.GlobalGeometry
namespace GS.SharedGeometry
variable {n : ℕ} {right left : Pattern n}

abbrev PairGenerator (right left : Pattern n) := Generator left × Generator right

/-- Spatial left and right generators; the plus sign absorbs the sign of
transposition in the group action. -/
def pointMap (right left : Pattern n) (X : Mat n) :
    PairGenerator right left →ₗ[ℝ] Mat n where
  toFun v := v.1.val * X + X * v.2.val
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a v := by
    change (a • v.1.val) * X + X * (a • v.2.val) =
      a • (v.1.val * X + X * v.2.val)
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add]

def pointDirections (right left : Pattern n) (X : Mat n) : Submodule ℝ (Mat n) :=
  LinearMap.range (pointMap right left X)

theorem mem_pointDirections_iff (X Y : Mat n) :
    Y ∈ pointDirections right left X ↔
      ∃ A ∈ sharedSkewSpace left.size left.label,
        ∃ B ∈ sharedSkewSpace right.size right.label, Y = A * X + X * B := by
  constructor
  · rintro ⟨⟨A, B⟩, h⟩
    exact ⟨A.val, A.property, B.val, B.property, h.symm⟩
  · rintro ⟨A, hA, B, hB, h⟩
    exact ⟨(⟨A, hA⟩, ⟨B, hB⟩), h.symm⟩

/-- Changing from body generators to spatial generators preserves all ties. -/
theorem sharedDirection_iff_pointDirections (P L R Y : Mat n)
    (hL : SharedOrthogonalFactor left.size left.label L)
    (hR : SharedOrthogonalFactor right.size right.label R) :
    SharedDirection right.size left.size right.label left.label P L R Y ↔
      Y ∈ pointDirections right left (product2 L P R) := by
  rw [mem_pointDirections_iff]
  constructor
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    refine ⟨L * C * Lᵀ, sharedSkew_conjugate left.positive left.divides hL hC,
      Rᵀ * Ω * R, sharedSkew_conjugate_transpose right.positive right.divides hR hΩ, ?_⟩
    have hl : (L * C * Lᵀ) * (L * P * R) = L * C * P * R := by
      calc
        _ = L * C * (Lᵀ * L) * P * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one]
    have hr : (L * P * R) * (Rᵀ * Ω * R) = L * P * Ω * R := by
      calc
        _ = L * P * (R * Rᵀ) * Ω * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.2]; simp only [Matrix.mul_one]
    simpa only [product2, hl, hr] using hY
  · rintro ⟨A, hA, B, hB, hY⟩
    refine ⟨Lᵀ * A * L,
      sharedSkew_conjugate_transpose left.positive left.divides hL hA,
      R * B * Rᵀ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
    have hl : L * (Lᵀ * A * L) * P * R = A * (L * P * R) := by
      calc
        _ = (L * Lᵀ) * A * (L * P * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.2]; simp only [Matrix.one_mul]
    have hr : L * P * (R * B * Rᵀ) * R = (L * P * R) * B := by
      calc
        _ = (L * P * R) * B * (Rᵀ * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.1, Matrix.mul_one]
    simpa only [product2, hl, hr] using hY

/-- The direction spaces transform under the actual shared group action. -/
theorem action_mem_pointDirections (g : Factors right left) (X Y : Mat n)
    (hY : Y ∈ pointDirections right left X) :
    g • Y ∈ pointDirections right left (g • X) := by
  obtain ⟨A, hA, B, hB, hY⟩ := (mem_pointDirections_iff X Y).mp hY
  let L := Factor.matrix g.1
  let R := Factor.matrix g.2
  have hL := Factor.matrix_shared g.1
  have hR := Factor.matrix_shared g.2
  apply (mem_pointDirections_iff (g • X) (g • Y)).mpr
  refine ⟨L * A * Lᵀ, sharedSkew_conjugate left.positive left.divides hL hA,
    R * B * Rᵀ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
  have hl : (L * A * Lᵀ) * (L * X * Rᵀ) = L * (A * X) * Rᵀ := by
    calc
      _ = L * A * (Lᵀ * L) * X * Rᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hr : (L * X * Rᵀ) * (R * B * Rᵀ) = L * (X * B) * Rᵀ := by
    calc
      _ = L * X * (Rᵀ * R) * B * Rᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  change L * Y * Rᵀ = (L * A * Lᵀ) * (L * X * Rᵀ) +
    (L * X * Rᵀ) * (R * B * Rᵀ)
  rw [hY, hl, hr, Matrix.mul_add, Matrix.add_mul]

end GS.SharedGeometry
