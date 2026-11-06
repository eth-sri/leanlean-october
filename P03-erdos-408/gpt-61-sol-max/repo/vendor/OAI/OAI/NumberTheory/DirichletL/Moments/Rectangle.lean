module

public import OAI.NumberTheory.DirichletL.Moments.Height

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentRectangle
open CenteredMomentPrimary CenteredMomentMask CenteredMomentTwist

def idealWeight (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (I : Ideal O)  :=
  (if IsCoprime I R then (1 : ℂ) else 0) *
    primaryIdealCharacter c χ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t)

def idealRectangle (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O)  :=
  W₁ ((Ideal.absNorm I : ℝ) / X₁) * W₂ ((Ideal.absNorm J : ℝ) / X₂) -
    W₁ ((Ideal.absNorm I : ℝ) / Y₁) * W₂ ((Ideal.absNorm J : ℝ) / Y₂)

end SevenEighths.CenteredMomentRectangle
end

end OAI
