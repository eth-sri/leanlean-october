module

public import GS.Extensions.MatrixCalculus

@[expose] public section

noncomputable section
open Matrix
namespace GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

def TwoFactorDirection (block₁ block₂ : Fin n → ℕ)
    (B₂ P B₁ X : Mat n) : Prop :=
  ∃ C Ω : Mat n, Supported block₂ C ∧ IsSkew C ∧
    Supported block₁ Ω ∧ IsSkew Ω ∧ X = tangentParam B₂ P B₁ C Ω

theorem isSkew_add {C K : Mat n} (hC : IsSkew C) (hK : IsSkew K) :
    IsSkew (C+K) := by
  unfold IsSkew at *
  rw [Matrix.transpose_add, hC, hK]
  abel

end GS.Extensions
