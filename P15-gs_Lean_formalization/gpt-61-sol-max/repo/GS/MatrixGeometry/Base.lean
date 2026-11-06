import Mathlib.Tactic
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
open Matrix
namespace GS.MatrixBase
variable {𝕜 : Type} [RCLike 𝕜]
variable (a : ℝ)

abbrev KMat (𝕜 : Type) (n : ℕ) := Matrix (Fin n) (Fin n) 𝕜
def Unitary {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι 𝕜) : Prop :=
  Aᴴ*A=1 ∧ A*Aᴴ=1

def IsSkewHermitian {n : ℕ} (A : KMat 𝕜 n) : Prop := Aᴴ = -A





namespace Unitary
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {A B : Matrix ι ι 𝕜}

theorem of_conjTranspose_mul (h : Aᴴ*A=1) : Unitary A := ⟨h,mul_eq_one_comm.mp h⟩
theorem one : Unitary (1 : Matrix ι ι 𝕜) := by constructor <;> simp

theorem conjTranspose (h : Unitary A) : Unitary Aᴴ := _root_.Unitary.star_mem h

theorem mul (hA : Unitary A) (hB : Unitary B) : Unitary (A*B) :=
  (unitary (Matrix ι ι 𝕜)).mul_mem hA hB

theorem submatrix (e : κ ≃ ι) (hA : Unitary A) : Unitary (A.submatrix e e) := by
  constructor <;> simp [Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,hA.1,hA.2]

end Unitary


/-- A complex matrix with entries only within equal block labels. -/
def CSupported {ι : Type*} (block : ι → ℕ) (A : Matrix ι ι 𝕜) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

namespace CSupported
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {block : ι → ℕ} {A B : Matrix ι ι 𝕜}
@[simp] theorem zero : CSupported block (0 : Matrix ι ι 𝕜) := by tauto
@[simp] theorem one : CSupported block (1 : Matrix ι ι 𝕜) := by
  intro i j hij
  have hne : i ≠ j := fun h => hij (congrArg block h)
  simp [ hne]
theorem conjTranspose (h : CSupported block A) : CSupported block Aᴴ := by
  intro i j hij
  simp [Matrix.conjTranspose_apply, h j i (Ne.symm hij)]
theorem add (hA : CSupported block A) (hB : CSupported block B) :
    CSupported block (A+B) := by
  intro i j hij
  simp [Matrix.add_apply, hA i j hij, hB i j hij]


theorem real_smul  (hA : CSupported block A) : CSupported block (a • A) := by
  intro i j hij
  simp [Matrix.smul_apply, hA i j hij]
theorem mul (hA : CSupported block A) (hB : CSupported block B) :
    CSupported block (A*B) := by
  intro i j hij
  change (∑ k, A i k * B k j) = 0
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : block i = block k
  · aesop
  · aesop

end CSupported






















def product2 (B₂ P B₁ : KMat 𝕜 n) : KMat 𝕜 n := B₂ * P * B₁

def tangentParam (B₂ P B₁ C Ω : KMat 𝕜 n) : KMat 𝕜 n :=
  B₂ * C * P * B₁ + B₂ * P * Ω * B₁








end GS.MatrixBase
