import GS.MatrixFactor.Permutations
import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Basic.Real.Star

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel



/-!
# Matrix objects from the manuscript

The mathematical scope is described in docs/PAPER_COVERAGE.md.

The matrices in this file really are finite real matrices. Orthogonality is
expressed by both Gram identities. In particular it is not an abstract tag.
-/

open Matrix

namespace GS

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def Orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop := Aᵀ * A = 1 ∧ A * Aᵀ = 1

namespace Orthogonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A B : Matrix ι ι ℝ}



theorem transpose (hA : Orthogonal A) : Orthogonal Aᵀ :=
  _root_.Unitary.star_mem hA

theorem mul (hA : Orthogonal A) (hB : Orthogonal B) : Orthogonal (A * B) :=
  (unitary (Matrix ι ι ℝ)).mul_mem hA hB

/-- Any square real matrix with one orthogonal Gram identity has both. -/
theorem of_transpose_mul (hA : Aᵀ * A = 1) : Orthogonal A := ⟨hA, mul_eq_one_comm.mp hA⟩

theorem of_mul_transpose (hA : A * Aᵀ = 1) : Orthogonal A := ⟨mul_eq_one_comm.mp hA, hA⟩

end Orthogonal

/-- Exact zero pattern: entries connecting different block labels vanish. -/
def Supported {ι : Type*} (block : ι → ℕ) (A : Matrix ι ι ℝ) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

/-- Consecutive, equal-size blocks, with the zero-based convention of the paper. -/
def BlockDiagonal {n : ℕ} (b : ℕ) (A : Mat n) : Prop :=
  Supported (fun i : Fin n => i.val / b) A

/-- Block sizes used in theorem statements are nonzero and divide the dimension. -/
structure BlockSpec (n : ℕ) where
  size : ℕ
  count : ℕ
  size_pos : 0 < size
  dimension : count * size = n

namespace Supported
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {block : ι → ℕ} {A B : Matrix ι ι ℝ}





theorem transpose (hA : Supported block A) : Supported block Aᵀ :=
  GS.MatrixBase.CSupported.conjTranspose hA





theorem mul (hA : Supported block A) (hB : Supported block B) :
    Supported block (A * B) :=
  GS.MatrixBase.CSupported.mul hA hB
end Supported

/-- The permutation matrix convention is P e_j = e_(sigma j). -/
def permMatrix {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι) : Matrix ι ι ℝ :=
  fun i j => if i = σ j then 1 else 0

section Permutations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem mul_perm_apply (A : Matrix ι ι ℝ) (σ : Equiv.Perm ι) (i j : ι) :
    (A * permMatrix σ) i j = A i (σ j) := GS.MatrixFactor.mul_cPerm_apply A σ i j

@[simp] theorem perm_mul_apply (σ : Equiv.Perm ι) (A : Matrix ι ι ℝ) (i j : ι) :
    (permMatrix σ * A) i j = A (σ.symm i) j := GS.MatrixFactor.cPerm_mul_apply σ A i j

@[simp] theorem perm_transpose (σ : Equiv.Perm ι) :
    (permMatrix σ)ᵀ = permMatrix σ.symm := GS.MatrixFactor.cPerm_conjTranspose σ

theorem perm_orthogonal (σ : Equiv.Perm ι) : Orthogonal (permMatrix σ) := GS.MatrixFactor.cPerm_unitary σ

/-- A permutation transports the block labels together with the zero pattern. -/
theorem supported_perm_conjugate_iff (block : ι → ℕ) (σ : Equiv.Perm ι)
    (A : Matrix ι ι ℝ) :
    Supported (block ∘ σ.symm) (permMatrix σ * A * (permMatrix σ)ᵀ) ↔
      Supported block A := by
  constructor
  · intro h i j hij
    have hz := h (σ i) (σ j) (by simpa using hij)
    simpa using hz
  · intro h i j hij
    simpa using h (σ.symm i) (σ.symm j) hij

end Permutations

/-- A concrete two-factor matrix expression. -/
def product2 {n} (B₂ P B₁ : Mat n) : Mat n := B₂ * P * B₁

def product3 {n} (B₃ P₂ B₂ P₁ B₁ : Mat n) : Mat n := B₃ * P₂ * B₂ * P₁ * B₁

def product4 {n} (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : Mat n) : Mat n := B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

def InA2 {n} (b₁ b₂ : ℕ) (P A : Mat n) : Prop :=
  ∃ B₁ B₂, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ A = product2 B₂ P B₁

def InA2Orth {n} (b₁ b₂ : ℕ) (P A : Mat n) : Prop :=
  ∃ B₁ B₂, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ A = product2 B₂ P B₁

def InA3 {n} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ BlockDiagonal b₃ B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

def InA3Orth {n} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ BlockDiagonal b₃ B₃ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ Orthogonal B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def InA4 {n} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    BlockDiagonal b₃ B₃ ∧ BlockDiagonal b₄ B₄ ∧ A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def InA4Orth {n} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : Mat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    BlockDiagonal b₃ B₃ ∧ BlockDiagonal b₄ B₄ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ Orthogonal B₃ ∧ Orthogonal B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁



end GS
