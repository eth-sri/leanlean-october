module

public import GS.Unitary.Support
public import GS.UnitaryCS.ColumnGram
public import GS.Unitary.Permutations
public import GS.Unitary.GeometryAlgebra

@[expose] public section


/-!
# Full two- and three-factor unitary factorization

These equivalences are unconditional: complex structured QR and RQ supply the
supported unitary outer factors. The middle factor is then unitary and block
triangular, hence block diagonal. Permutation connectors are arbitrary, and
the statements allow all natural block sizes without extra divisibility
assumptions.
-/

noncomputable section

namespace GS.UnitaryGeometry
variable {n : ℕ}

def CBlockDiagonal (b : ℕ) (A : CMat n) : Prop :=
  CSupported (fun i : Fin n => i.val / b) A

def product3 (B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₃ * P₂ * B₂ * P₁ * B₁

section
variable (b₁ b₂ : ℕ) (P A : CMat n)
def CInA2 : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    A = product2 B₂ P B₁

def CInA2Unitary : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ A = product2 B₂ P B₁

end

section
variable (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n)
def CInA3 : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def CInA3Unitary : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁







end

end GS.UnitaryGeometry
