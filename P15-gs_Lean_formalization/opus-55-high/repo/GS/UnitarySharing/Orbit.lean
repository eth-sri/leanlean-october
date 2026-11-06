module

public import GS.Unitary.GeometryAlgebra
public import GS.ComplexAlgebra

@[expose] public section

/-! # Statement-level definitions for complex complete-block sharing -/

open Matrix GS GS.UnitaryGeometry
namespace GS.UnitarySharing
variable {n : ℕ}

section
variable (b : ℕ) (τ : ℕ → ℕ) (A : CMat n)
/-- Labels tie full complex blocks within one layer, never across layers. -/
def TiedEntries : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

def SharedUnitaryFactor : Prop :=
  CSupported (fun i => i.val / b) A ∧ Unitary A ∧ TiedEntries b τ A

end

/-- Actual two-layer family with full within-layer unitary block sharing. -/
def InSharedA2Unitary (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : CMat n) : Prop :=
  ∃ L R : CMat n, SharedUnitaryFactor b₂ τ₂ L ∧
    SharedUnitaryFactor b₁ τ₁ R ∧ X = GS.UnitaryGeometry.product2 L P R

end GS.UnitarySharing
