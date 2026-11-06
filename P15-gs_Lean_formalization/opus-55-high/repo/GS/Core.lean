module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section


/-!
# Matrix objects from the manuscript

The mathematical scope is described in docs/PAPER_COVERAGE.md.

The matrices in this file really are finite real matrices. Orthogonality is
expressed by both Gram identities. In particular it is not an abstract tag.
-/

noncomputable section
open Matrix

namespace GS

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def Orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop := Aᵀ * A = 1 ∧ A * Aᵀ = 1

namespace Orthogonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A B : Matrix ι ι ℝ}


theorem transpose (hA : Orthogonal A) : Orthogonal Aᵀ := by
  simpa [Orthogonal] using hA.symm

theorem mul (hA : Orthogonal A) (hB : Orthogonal B) : Orthogonal (A * B) := by
  constructor <;> simp [Matrix.mul_assoc, ← Matrix.mul_assoc B, ← Matrix.mul_assoc Aᵀ, hA.1, hA.2, hB.1, hB.2]

/-- Any square real matrix with one orthogonal Gram identity has both. -/
theorem of_transpose_mul (hA : Aᵀ * A = 1) : Orthogonal A :=
  ⟨hA, mul_eq_one_comm.mp hA⟩

theorem of_mul_transpose (hA : A * Aᵀ = 1) : Orthogonal A :=
  ⟨mul_eq_one_comm.mp hA, hA⟩

end Orthogonal

/-- Exact zero pattern: entries connecting different block labels vanish. -/
def Supported (block : ι → ℕ) (A : Matrix ι ι ℝ) : Prop :=
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

@[simp] theorem zero : Supported block (0 : Matrix ι ι ℝ) := by tauto

@[simp] theorem one : Supported block (1 : Matrix ι ι ℝ) := by
  intro i j hij
  simp [show i ≠ j by grind]

theorem transpose (hA : Supported block A) : Supported block Aᵀ := by
  tauto

theorem add (hA : Supported block A) (hB : Supported block B) :
    Supported block (A + B) := by
  intro i j hij
  simp [hA i j hij, hB i j hij]


theorem smul (a : ℝ) (hA : Supported block A) : Supported block (a • A) := fun i j h => by aesop

theorem mul (hA : Supported block A) (hB : Supported block B) :
    Supported block (A * B) := fun i j _ =>
  Finset.sum_eq_zero fun t _ => by by_cases block i = block t <;> aesop

end Supported

/-- The permutation matrix convention is P e_j = e_(sigma j). -/
def permMatrix {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι) : Matrix ι ι ℝ :=
  fun i j => if i = σ j then 1 else 0

section Permutations
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem mul_perm_apply (A : Matrix ι ι ℝ) (σ : Equiv.Perm ι) (i j : ι) :
    (A * permMatrix σ) i j = A i (σ j) := by
  simp [Matrix.mul_apply, permMatrix]

section
variable (σ : Equiv.Perm ι)
@[simp] theorem perm_mul_apply (A : Matrix ι ι ℝ) (i j : ι) :
    (permMatrix σ * A) i j = A (σ.symm i) j := by
  simp [Matrix.mul_apply, permMatrix, ← Equiv.symm_apply_eq]

@[simp] theorem perm_transpose :
    (permMatrix σ)ᵀ = permMatrix σ.symm := by
  ext i j
  simp [permMatrix, Equiv.eq_symm_apply, eq_comm]

theorem perm_orthogonal : Orthogonal (permMatrix σ) := by
  constructor <;> ext i j <;>
    simp [perm_transpose, permMatrix, Matrix.one_apply]


end

/-- A permutation transports the block labels together with the zero pattern. -/
theorem supported_perm_conjugate_iff (block : ι → ℕ) (σ : Equiv.Perm ι)
    (A : Matrix ι ι ℝ) :
    Supported (block ∘ σ.symm) (permMatrix σ * A * (permMatrix σ)ᵀ) ↔
      Supported block A := by
  refine ⟨fun h i j hij => ?_, fun h i j hij => by aesop⟩
  simpa using h (σ i) (σ j) (by simpa)

end Permutations

section
variable {n}
/-- A concrete two-factor matrix expression. -/
def product2 (B₂ P B₁ : Mat n) : Mat n := B₂ * P * B₁

def product3 (B₃ P₂ B₂ P₁ B₁ : Mat n) : Mat n := B₃ * P₂ * B₂ * P₁ * B₁

def product4 (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : Mat n) : Mat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

end

section
variable {n} (b₁ b₂ : ℕ) (P A : Mat n)
def InA2 : Prop :=
  ∃ B₁ B₂, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ A = product2 B₂ P B₁

def InA2Orth : Prop :=
  ∃ B₁ B₂, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ A = product2 B₂ P B₁

end

section
variable {n} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : Mat n)
def InA3 : Prop :=
  ∃ B₁ B₂ B₃, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ BlockDiagonal b₃ B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

def InA3Orth : Prop :=
  ∃ B₁ B₂ B₃, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧ BlockDiagonal b₃ B₃ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ Orthogonal B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

end

section
variable {n} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : Mat n)
def InA4 : Prop :=
  ∃ B₁ B₂ B₃ B₄, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    BlockDiagonal b₃ B₃ ∧ BlockDiagonal b₄ B₄ ∧ A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def InA4Orth : Prop :=
  ∃ B₁ B₂ B₃ B₄, BlockDiagonal b₁ B₁ ∧ BlockDiagonal b₂ B₂ ∧
    BlockDiagonal b₃ B₃ ∧ BlockDiagonal b₄ B₄ ∧
    Orthogonal B₁ ∧ Orthogonal B₂ ∧ Orthogonal B₃ ∧ Orthogonal B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁


end

end GS
