module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
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
public import GS.Core
public import GS.Extensions.GeodesicNormal
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Extensions.TwoFactorProjection
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.LieAction.Action
public import GS.LieAction.BlockGroup
public import GS.LieAction.Nonoverlap
public import GS.ManifoldCompletion.OrbitDifferential
public import GS.OverlapGeometry.HorizontalModel
public import GS.Projection
public import GS.Shuffle
public import GS.Unitary.CholeskySupport
public import GS.Unitary.Factorization
public import GS.Unitary.Frobenius
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.OrdinaryQR
public import GS.Unitary.Permutations
public import GS.Unitary.Projection
public import GS.Unitary.StructuredQR
public import GS.Unitary.Support
public import GS.UnitaryLocalModel.Dephasing
public import GS.UnitaryManifold.Action
public import GS.UnitaryManifold.BlockGroup
public import GS.UnitaryManifold.CayleyAlgebra
public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.CayleyDifferential
public import GS.UnitaryManifold.CayleyModel
public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.Factors
public import GS.UnitaryManifold.HorizontalModel
public import GS.UnitaryManifold.KernelCayley
public import GS.UnitaryManifold.LocalProduct
public import GS.UnitaryManifold.MatrixCalculus


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The surjective derivative of the dephasing constraints

The anchor constraints are applied to the actual full-unitary Cayley chart.
Explicit row and column phase generators provide a right inverse for their
derivative. No regularity assumption about squared entry moduli is used.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped Topology
namespace GS.UnitaryLocalModel
variable {q : ℕ}

abbrev FullUnitary (q : ℕ) := BlockU (fun _ : Fin q => 0)
abbrev FullSkewModel (q : ℕ) := Model (fun _ : Fin q => 0)
abbrev AnchorCoordinates (o : Fin q) :=
  (Fin q → ℝ) × ({j : Fin q // j ≠ o} → ℝ)

def fullUnitary (Q : CMat q) (hQ : Unitary Q) : FullUnitary q :=
  ⟨Q, (by intro i j hij; exact (hij rfl).elim), hQ⟩

/-- Imaginary parts of the independent anchor ratios. -/
def anchorImagLinear (Q : CMat q) (o : Fin q) : CMat q →ₗ[ℝ] AnchorCoordinates o where
  toFun A := (fun i => (A i o / Q i o).im, fun j => (A o j.val / Q o j.val).im)
  map_add' A B := by
    apply Prod.ext <;> funext i <;> simp [add_div, Complex.add_im]
  map_smul' r A := by
    apply Prod.ext <;> funext i <;>
      simp [Complex.real_smul, mul_div_assoc, Complex.mul_im]

def anchorImag (Q : CMat q) (o : Fin q) : CMat q →L[ℝ] AnchorCoordinates o :=
  (anchorImagLinear Q o).toContinuousLinearMap

@[simp] theorem anchorImag_apply (Q A : CMat q) (o : Fin q) :
    anchorImag Q o A =
      (fun i => (A i o / Q i o).im, fun j => (A o j.val / Q o j.val).im) := rfl

def anchorConstraints (Q : FullUnitary q) (o : Fin q) (x : FullSkewModel q) :
    AnchorCoordinates o := anchorImag Q.val o (chartInv Q x)

theorem anchorConstraints_smooth (Q : FullUnitary q) (o : Fin q) :
    ContDiff ℝ ⊤ (anchorConstraints Q o) :=
  (anchorImag Q.val o).contDiff.comp (chartInv_smooth Q)

@[simp] theorem anchorConstraints_zero (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : anchorConstraints Q o 0 = 0 := by
  rw [anchorConstraints, chartInv_zero]
  apply Prod.ext
  · funext i
    simp [anchorImag_apply, div_self (hQ.1 i).1]
  · funext j
    simp [anchorImag_apply, div_self (hQ.2 j.val).1]

def anchorDerivative (Q : FullUnitary q) (o : Fin q) :
    FullSkewModel q →L[ℝ] AnchorCoordinates o :=
  (anchorImag Q.val o).comp (fderiv ℝ (chartInv Q) 0)

theorem anchorConstraints_hasFDerivAt (Q : FullUnitary q) (o : Fin q) :
    HasFDerivAt (anchorConstraints Q o) (anchorDerivative Q o) 0 :=
  ((anchorImag Q.val o).hasFDerivAt).comp 0
    ((chartInv_smooth Q).differentiable (by simp) 0).hasFDerivAt

theorem anchorConstraints_hasStrictFDerivAt (Q : FullUnitary q) (o : Fin q) :
    HasStrictFDerivAt (anchorConstraints Q o) (anchorDerivative Q o) 0 :=
  (anchorConstraints_smooth Q o).contDiffAt.hasStrictFDerivAt'
    (anchorConstraints_hasFDerivAt Q o) (by simp)

/-- Infinitesimal diagonal phases. -/
def phaseDiagonal (a : Fin q → ℝ) : CMat q :=
  Matrix.diagonal (fun i => (a i : ℂ) * Complex.I)

theorem phaseDiagonal_skew (a : Fin q → ℝ) : IsSkewHermitian (phaseDiagonal a) := by
  unfold IsSkewHermitian phaseDiagonal
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_neg]
  have he : (fun i => star ((a i : ℂ) * Complex.I)) =
      (fun i => -((a i : ℂ) * Complex.I)) := by
    funext i
    simp
  exact congrArg Matrix.diagonal he

/-- A Cayley coordinate whose velocity is the prescribed row/column phase variation. -/
def phaseCoordinate (Q : FullUnitary q) (a b : Fin q → ℝ) : FullSkewModel q :=
  ⟨(-1 / 2 : ℝ) • (Q.valᴴ * phaseDiagonal a * Q.val + phaseDiagonal b),
    (by intro i j hij; exact (hij rfl).elim),
    skewHermitian_real_smul _ (skewHermitian_add
      (by simpa using conjugate_skewHermitian Q.valᴴ (phaseDiagonal a) (phaseDiagonal_skew a))
      (phaseDiagonal_skew b))⟩

theorem phaseCoordinate_velocity (Q : FullUnitary q) (a b : Fin q → ℝ) :
    fderiv ℝ (chartInv Q) 0 (phaseCoordinate Q a b) =
      phaseDiagonal a * Q.val + Q.val * phaseDiagonal b := by
  rw [chartInv_fderiv_zero]
  change (-2 : ℝ) • (Q.val * ((-1 / 2 : ℝ) •
    (Q.valᴴ * phaseDiagonal a * Q.val + phaseDiagonal b))) = _
  rw [Matrix.mul_smul, smul_smul]
  norm_num
  rw [Matrix.mul_add]
  congr 1
  simp only [← Matrix.mul_assoc, Q.property.2.2, Matrix.one_mul]

theorem phaseCoordinate_constraints (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) (a : Fin q → ℝ) (b : zeroAnchorSpace o) :
    anchorDerivative Q o (phaseCoordinate Q a b.val) = phaseConstraintMap o (a,b) := by
  change anchorImag Q.val o (fderiv ℝ (chartInv Q) 0 (phaseCoordinate Q a b.val)) = _
  rw [phaseCoordinate_velocity]
  have hb : b.val o = 0 := b.property
  apply Prod.ext
  · funext i
    change (((phaseDiagonal a * Q.val + Q.val * phaseDiagonal b.val) i o) / Q.val i o).im = a i
    simp only [Matrix.add_apply, phaseDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, hb,
      Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
    rw [mul_div_cancel_right₀ _ (hQ.1 i).1]
    simp
  · funext j
    change (((phaseDiagonal a * Q.val + Q.val * phaseDiagonal b.val) o j.val) /
      Q.val o j.val).im = a o + b.val j.val
    simp only [Matrix.add_apply, phaseDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [add_div, mul_div_cancel_right₀ _ (hQ.2 j.val).1,
      mul_div_cancel_left₀ _ (hQ.2 j.val).1]
    simp

/-- Surjectivity is proved by explicit phase directions, not assumed. -/
theorem anchorDerivative_surjective (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : Function.Surjective (anchorDerivative Q o) := by
  intro y
  obtain ⟨⟨a,b⟩, hab⟩ := phaseConstraintMap_surjective o y
  exact ⟨phaseCoordinate Q a b.val, (phaseCoordinate_constraints Q o hQ a b).trans hab⟩

theorem anchorDerivative_range (Q : FullUnitary q) (o : Fin q)
    (hQ : AnchorNonzero Q.val Q.val o) : LinearMap.range (anchorDerivative Q o : FullSkewModel q →ₗ[ℝ] AnchorCoordinates o) = ⊤ :=
  LinearMap.range_eq_top.mpr (anchorDerivative_surjective Q o hQ)

end GS.UnitaryLocalModel
