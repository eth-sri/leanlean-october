module

public import GS.Core
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

noncomputable section

/-! Complex matrix families with block support, fixed carriers, and optional block sharing. -/
open Matrix

namespace GS

abbrev CMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def Unitary {n : ℕ} (A : CMat n) : Prop := Aᴴ*A=1 ∧ A*Aᴴ=1

end GS

namespace GS.UnitaryGeometry
variable {n : ℕ}

/-- A complex matrix with entries only within equal block labels. -/
def CSupported (block : Fin n → ℕ) (A : CMat n) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0


def cPermMatrix (σ : Equiv.Perm (Fin n)) : CMat n :=
  fun i j => if i = σ j then 1 else 0


def product2 (B₂ P B₁ : CMat n) : CMat n := B₂ * P * B₁


def CBlockDiagonal (b : ℕ) (A : CMat n) : Prop :=
  CSupported (fun i : Fin n => i.val / b) A

def product3 (B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₃ * P₂ * B₂ * P₁ * B₁

def CInA2 (b₁ b₂ : ℕ) (P A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    A = product2 B₂ P B₁

def CInA2Unitary (b₁ b₂ : ℕ) (P A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ A = product2 B₂ P B₁

def CInA3 (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def CInA3Unitary (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

end GS.UnitaryGeometry

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
