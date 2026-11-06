module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
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
public import Mathlib.Topology.Order.Compact
public import GS.CompactFibres
public import GS.ComplexAlgebra
public import GS.Continuation.AmbientProjection
public import GS.Continuation.ExponentialBasics
public import GS.Core
public import GS.Extensions.FiniteTopology
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
public import GS.OriginalLocalModel
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
public import GS.UnitaryManifold.CayleyModel
public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitarySharing.Algebra
public import GS.UnitarySharing.Factors
public import GS.UnitarySharing.Orbit


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
shared-orbit atlas and identification with its manifold differential are
constructed in the later atlas and tangent-bridge modules.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
namespace GS.UnitarySharing
variable {n : ℕ} {right left : Pattern n}

abbrev PairGenerator (right left : Pattern n) := Generator left × Generator right

/-- Spatial left and right generators; the plus sign absorbs the sign of
transposition in the group action. -/
def pointMap (right left : Pattern n) (X : CMat n) :
    PairGenerator right left →ₗ[ℝ] CMat n where
  toFun v := v.1.val * X + X * v.2.val
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' a v := by
    change (a • v.1.val) * X + X * (a • v.2.val) =
      a • (v.1.val * X + X * v.2.val)
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_add]

def pointDirections (right left : Pattern n) (X : CMat n) : Submodule ℝ (CMat n) :=
  LinearMap.range (pointMap right left X)

theorem mem_pointDirections_iff (X Y : CMat n) :
    Y ∈ pointDirections right left X ↔
      ∃ A ∈ sharedSkewSpace left.size left.label,
        ∃ B ∈ sharedSkewSpace right.size right.label, Y = A * X + X * B := by
  constructor
  · rintro ⟨⟨A, B⟩, h⟩
    exact ⟨A.val, A.property, B.val, B.property, h.symm⟩
  · rintro ⟨A, hA, B, hB, h⟩
    exact ⟨(⟨A, hA⟩, ⟨B, hB⟩), h.symm⟩

/-- Complete synthesis: equalities between repeated entries do not remove
nonoverlap residuals from a coupled least-squares problem. -/
def SharedDirection (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Y : CMat n) : Prop :=
  ∃ C ∈ sharedSkewSpace b₂ τ₂, ∃ Ω ∈ sharedSkewSpace b₁ τ₁,
    Y = L * C * P * R + L * P * Ω * R

/-- Changing from body generators to spatial generators preserves all ties. -/
theorem sharedDirection_iff_pointDirections (P L R Y : CMat n)
    (hL : SharedUnitaryFactor left.size left.label L)
    (hR : SharedUnitaryFactor right.size right.label R) :
    SharedDirection right.size left.size right.label left.label P L R Y ↔
      Y ∈ pointDirections right left (GS.UnitaryGeometry.product2 L P R) := by
  rw [mem_pointDirections_iff]
  constructor
  · rintro ⟨C, hC, Ω, hΩ, hY⟩
    refine ⟨L * C * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hC,
      Rᴴ * Ω * R, sharedSkew_conjugate_conjTranspose right.positive right.divides hR hΩ, ?_⟩
    have hl : (L * C * Lᴴ) * (L * P * R) = L * C * P * R := by
      calc
        _ = L * C * (Lᴴ * L) * P * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one]
    have hr : (L * P * R) * (Rᴴ * Ω * R) = L * P * Ω * R := by
      calc
        _ = L * P * (R * Rᴴ) * Ω * R := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.2]; simp only [Matrix.mul_one]
    simpa only [GS.UnitaryGeometry.product2, hl, hr] using hY
  · rintro ⟨A, hA, B, hB, hY⟩
    refine ⟨Lᴴ * A * L,
      sharedSkew_conjugate_conjTranspose left.positive left.divides hL hA,
      R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
    have hl : L * (Lᴴ * A * L) * P * R = A * (L * P * R) := by
      calc
        _ = (L * Lᴴ) * A * (L * P * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hL.2.1.2]; simp only [Matrix.one_mul]
    have hr : L * P * (R * B * Rᴴ) * R = (L * P * R) * B := by
      calc
        _ = (L * P * R) * B * (Rᴴ * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hR.2.1.1, Matrix.mul_one]
    simpa only [GS.UnitaryGeometry.product2, hl, hr] using hY

/-- The direction spaces transform under the actual shared group action. -/
theorem action_mem_pointDirections (g : Factors right left) (X Y : CMat n)
    (hY : Y ∈ pointDirections right left X) :
    g • Y ∈ pointDirections right left (g • X) := by
  obtain ⟨A, hA, B, hB, hY⟩ := (mem_pointDirections_iff X Y).mp hY
  let L := Factor.matrix g.1
  let R := Factor.matrix g.2
  have hL := Factor.matrix_shared g.1
  have hR := Factor.matrix_shared g.2
  apply (mem_pointDirections_iff (g • X) (g • Y)).mpr
  refine ⟨L * A * Lᴴ, sharedSkew_conjugate left.positive left.divides hL hA,
    R * B * Rᴴ, sharedSkew_conjugate right.positive right.divides hR hB, ?_⟩
  have hl : (L * A * Lᴴ) * (L * X * Rᴴ) = L * (A * X) * Rᴴ := by
    calc
      _ = L * A * (Lᴴ * L) * X * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hL.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hr : (L * X * Rᴴ) * (R * B * Rᴴ) = L * (X * B) * Rᴴ := by
    calc
      _ = L * X * (Rᴴ * R) * B * Rᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR.2.1.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  change L * Y * Rᴴ = (L * A * Lᴴ) * (L * X * Rᴴ) +
    (L * X * Rᴴ) * (R * B * Rᴴ)
  rw [hY, hl, hr, Matrix.mul_add, Matrix.add_mul]

end GS.UnitarySharing
