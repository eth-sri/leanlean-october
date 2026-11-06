
import GS.Unitary.StructuredQR
import GS.Unitary.GeometryAlgebra



/-!
# Full two- and three-factor unitary factorization

These equivalences are unconditional: complex structured QR and RQ supply the
supported unitary outer factors. The middle factor is then unitary and block
triangular, hence block diagonal. Permutation connectors are arbitrary, and
the statements allow all natural block sizes without extra divisibility
assumptions.
-/


namespace GS.UnitaryGeometry

variable (b b₁ b₂ b₃ : ℕ)

variable (A B₃ P₂ B₂ P₁ B₁ P : CMat n)

def CBlockDiagonal   : Prop :=
  CSupported (fun i : Fin n => i.val / b) A

def product3  : CMat n :=
  B₃ * P₂ * B₂ * P₁ * B₁

def CInA2  (A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    A = product2 B₂ P B₁

def CInA2Unitary  (A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ A = product2 B₂ P B₁

def CInA3  (P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def CInA3Unitary  (P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁













end GS.UnitaryGeometry
