module

public import GS.Isometric.Families
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

/-! The real and complex statement vocabulary specializes the same entrywise families. -/
noncomputable section
open Matrix
namespace GS

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def Orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop := Aᵀ * A = 1 ∧ A * Aᵀ = 1

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

/-- The permutation matrix convention is P e_j = e_(sigma j). -/
def permMatrix {ι : Type*} [DecidableEq ι] (σ : Equiv.Perm ι) : Matrix ι ι ℝ :=
  fun i j => if i = σ j then 1 else 0

/-- A concrete two-factor matrix expression. -/
def product2 {n} (B₂ P B₁ : Mat n) : Mat n := B₂ * P * B₁

def product3 {n} (B₃ P₂ B₂ P₁ B₁ : Mat n) : Mat n := B₃ * P₂ * B₂ * P₁ * B₁

def product4 {n} (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : Mat n) : Mat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

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

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def Unitary {n : ℕ} (A : CMat n) : Prop := Aᴴ*A=1 ∧ A*Aᴴ=1

namespace UnitaryGeometry

def product2 {n : ℕ} (B₂ P B₁ : CMat n) : CMat n := B₂ * P * B₁

def CSupported {n : ℕ} (block : Fin n → ℕ) (A : CMat n) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

def cPermMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : CMat n :=
  fun i j => if i = σ j then 1 else 0

def CBlockDiagonal {n : ℕ} (b : ℕ) (A : CMat n) : Prop :=
  CSupported (fun i : Fin n => i.val / b) A

def product3 {n : ℕ} (B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₃ * P₂ * B₂ * P₁ * B₁

def CInA2 {n : ℕ} (b₁ b₂ : ℕ) (P A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    A = product2 B₂ P B₁

def CInA2Unitary {n : ℕ} (b₁ b₂ : ℕ) (P A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ A = product2 B₂ P B₁

def CInA3 {n : ℕ} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def CInA3Unitary {n : ℕ} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

def product4 {n : ℕ} (B₄ P₃ B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₄ * P₃ * B₃ * P₂ * B₂ * P₁ * B₁

def CInA4 {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

def CInA4Unitary {n : ℕ} (b₁ b₂ b₃ b₄ : ℕ) (P₁ P₂ P₃ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃ B₄, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ CBlockDiagonal b₄ B₄ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧ Unitary B₄ ∧
    A = product4 B₄ P₃ B₃ P₂ B₂ P₁ B₁

end UnitaryGeometry

end GS

namespace GS.GlobalGeometry

/-- Complete physical blocks carrying the same label have identical entries. -/
def TiedEntries {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.Mat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

/-- An orthogonal block diagonal layer with complete within-layer sharing. -/
def SharedOrthogonalFactor {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.Mat n) : Prop :=
  GS.BlockDiagonal b A ∧ GS.Orthogonal A ∧ TiedEntries b τ A

/-- The actual two-layer image; the carrier P may be singular. -/
def InSharedA2Orth {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : GS.Mat n) : Prop :=
  ∃ L R, SharedOrthogonalFactor b₂ τ₂ L ∧ SharedOrthogonalFactor b₁ τ₁ R ∧
    X = GS.product2 L P R

end GS.GlobalGeometry

namespace GS.UnitarySharing

/-- Complete equal-size complex blocks tied by their layer labels. -/
def TiedEntries {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.CMat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

/-- A unitary layer subject to its physical block support and sharing. -/
def SharedUnitaryFactor {n : ℕ} (b : ℕ) (τ : ℕ → ℕ) (A : GS.CMat n) : Prop :=
  GS.UnitaryGeometry.CSupported (fun i => i.val / b) A ∧ GS.Unitary A ∧ TiedEntries b τ A

/-- The actual shared two-layer unitary image. -/
def InSharedA2Unitary {n : ℕ} (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : GS.CMat n) : Prop :=
  ∃ L R, SharedUnitaryFactor b₂ τ₂ L ∧ SharedUnitaryFactor b₁ τ₁ R ∧
    X = GS.UnitaryGeometry.product2 L P R

end GS.UnitarySharing
