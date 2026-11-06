module

public import OAI.NumberTheory.DirichletL.Hecke.RayFamily
public import OAI.NumberTheory.DirichletL.RayQuotient

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayQuotient
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def character (χ : RayQuotient.Characters M H)  :=
  HeckeRayFamily.character M (RayQuotient.toFullRay M H hH χ)

theorem idealCoeff_character  χ   I  :
    idealCoeff (character M H hH χ) I = RayQuotient.idealCharacter M H hH χ I := rfl

theorem average_idealCoeff  I  :
    (RayQuotient.classNumber M H : ℂ)⁻¹ *
      ∑ χ : RayQuotient.Characters M H, idealCoeff (character M H hH χ) I =
      if I ∈ RayQuotient.identityClass M H then 1 else 0 := by
  simp only [idealCoeff_character]
  simpa only [div_eq_mul_inv, mul_comm] using RayQuotient.average_idealCharacters M H hH I

end SevenEighths.HeckeRayQuotient

end

end OAI
