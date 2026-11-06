module
public import OAI.NumberTheory.DirichletL.RayOrthogonality
public import OAI.NumberTheory.DirichletL.Hecke.LogDerivative

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayFamily
open HeckeFamily

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def character (χ : RayOrthogonality.rayCharacters M) : Character :=
  Character.ofResidue M (NeZero.ne M) χ.val ((RayOrthogonality.mem_rayCharacters_iff M χ.val).mp χ.property)

section
variable (χ : RayOrthogonality.rayCharacters M)
include χ
theorem idealCoeff_character (I : Ideal O) :
    idealCoeff (character M χ) I = RayOrthogonality.idealCharacter M χ I := rfl

theorem principal_iff :
    (character M χ).residue = 1 ↔ χ = 1 := by aesop

theorem character_entire (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M χ)) :=
  LFunction_entire_nonprincipal _ (fun h => hχ ((principal_iff M χ).mp h))

theorem character_boundary_ne_zero
    {s : ℂ} (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M χ) s ≠ 0 := by
  apply LFunction_ne_zero_of_one_le_re _ hs
  aesop
end

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ rfl

end SevenEighths.HeckeRayFamily

end

end OAI
