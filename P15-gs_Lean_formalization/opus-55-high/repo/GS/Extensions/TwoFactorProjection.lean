module

public import GS.Extensions.MatrixCalculus

@[expose] public section


/-!
# Connect the supported-skew projector to the two-factor differential image

No sharing is imposed in this module.
Both overlapping and nonoverlapping supports are treated exactly. The range is
the image of an actual Frechet derivative on specified generator directions;
this module does not yet identify it with an embedded manifold tangent space.
-/

noncomputable section
namespace GS.Extensions

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}







 def TwoFactorDirection (block₁ block₂ : Fin n → ℕ)
    (B₂ P B₁ X : Mat n) : Prop :=
  ∃ C Ω : Mat n, Supported block₂ C ∧ IsSkew C ∧
    Supported block₁ Ω ∧ IsSkew Ω ∧ X = tangentParam B₂ P B₁ C Ω

 theorem isSkew_add {C K : Mat n} (hC : IsSkew C) (hK : IsSkew K) :
    IsSkew (C+K) := by
  simp_all [IsSkew, add_comm]





end GS.Extensions
