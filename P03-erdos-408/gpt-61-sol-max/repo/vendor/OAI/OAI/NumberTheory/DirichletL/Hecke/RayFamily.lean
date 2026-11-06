module
public import Mathlib.Tactic

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

def character (χ : RayOrthogonality.rayCharacters M)  :=
  Character.ofResidue M (NeZero.ne M) χ.val ((RayOrthogonality.mem_rayCharacters_iff M χ.val).mp χ.property)

theorem idealCoeff_character  χ   I  :
    idealCoeff (character M χ) I = RayOrthogonality.idealCharacter M χ I := rfl



theorem character_entire  χ  (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M χ)) :=
  OAI.SevenEighths.HeckeFamily.LFunction_entire_nonprincipal (OAI.SevenEighths.HeckeRayFamily.character M χ) fun h => hχ (Subtype.ext h)

theorem character_boundary_ne_zero  χ 
     {s}  (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M χ) s ≠ 0 := OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_one_le_re (OAI.SevenEighths.HeckeRayFamily.character M χ) hs (Or.imp id (fun h hn => h (Subtype.ext hn)) hpole)

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ rfl

end SevenEighths.HeckeRayFamily

end

end OAI
