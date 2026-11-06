module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.Order.Compact
public import GS.ComplexAlgebra
public import GS.Core
public import GS.Frobenius
public import GS.Unitary.Frobenius
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.Projection
public import GS.Unitary.Support
public import GS.UnitaryManifold.BlockGroup
public import GS.UnitaryManifold.CayleyAlgebra
public import GS.UnitaryManifold.CayleyCharts
public import GS.UnitaryManifold.CayleyDifferential
public import GS.UnitaryManifold.CayleyModel
public import GS.UnitaryManifold.CayleySmooth
public import GS.UnitaryManifold.MatrixCalculus


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The normalized unitary Cayley transform

The normalization gives derivative equal to the identity. All denominators
are invertible for every skew-Hermitian argument, without a step-size bound.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {n : ℕ}

/-- Cayley normalization with derivative +identity at zero. -/
def unitCayley (A : CMat n) : CMat n := cayley ((-1 / 2 : ℝ) • A)

@[simp] theorem unitCayley_zero : unitCayley (0 : CMat n) = 1 := by
  simp [unitCayley]

theorem unitCayley_smooth_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → CMat n) (hs : ContDiff ℝ ⊤ A) (hk : ∀ x, IsSkewHermitian (A x)) :
    ContDiff ℝ ⊤ (fun x => unitCayley (A x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  change ContDiffAt ℝ ⊤ (fun y => cayley ((-1 / 2 : ℝ) • A y)) x
  apply smooth_cayley_comp_at (hs.contDiffAt.const_smul (-1 / 2 : ℝ))
  exact admissible_of_isSkew _ (skewHermitian_real_smul _ (hk x))

/-- The matrix curve differential follows from the already checked Cayley chart. -/
theorem cayley_line_derivative (A : CMat n) (hk : IsSkewHermitian A) :
    HasDerivAt (fun t : ℝ => cayley (t • A)) ((-2 : ℝ) • A) 0 := by
  let u : Model (fun _ : Fin n => 0) := ⟨A, by intro i j hij; exact (hij rfl).elim, hk⟩
  have hd := chartInv_line_hasDerivAt_zero (1 : BlockU (fun _ : Fin n => 0)) u
  simpa only [chartInv, blockU_one_val, Matrix.one_mul, Submodule.coe_smul] using hd

theorem unitCayley_line_derivative (A : CMat n) (hk : IsSkewHermitian A) :
    HasDerivAt (fun t : ℝ => unitCayley (t • A)) A 0 := by
  have hd := cayley_line_derivative ((-1 / 2 : ℝ) • A) (skewHermitian_real_smul _ hk)
  have hf : (fun t : ℝ => unitCayley (t • A)) =
      (fun t : ℝ => cayley (t • ((-1 / 2 : ℝ) • A))) := by
    funext t
    unfold unitCayley
    rw [smul_comm]
  rw [hf]
  simpa only [smul_smul, show (-2 : ℝ) * (-1 / 2) = 1 by norm_num, one_smul] using hd

end GS.UnitaryManifold
