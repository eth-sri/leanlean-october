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

def character (χ : RayOrthogonality.rayCharacters M) : Character :=
  Character.ofResidue M (NeZero.ne M) χ.val ((RayOrthogonality.mem_rayCharacters_iff M χ.val).mp χ.property)

theorem idealCoeff_character (χ : RayOrthogonality.rayCharacters M) (I : Ideal O) :
    idealCoeff (character M χ) I = RayOrthogonality.idealCharacter M χ I := rfl

theorem principal_iff (χ : RayOrthogonality.rayCharacters M) :
    (character M χ).residue = 1 ↔ χ = 1 := by
  change χ.val = 1 ↔ χ = 1
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem character_entire (χ : RayOrthogonality.rayCharacters M) (hχ : χ ≠ 1) :
    Differentiable ℂ (LFunction (character M χ)) :=
  LFunction_entire_nonprincipal _ (fun h => hχ ((principal_iff M χ).mp h))

theorem character_boundary_ne_zero (χ : RayOrthogonality.rayCharacters M)
    {s : ℂ} (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    LFunction (character M χ) s ≠ 0 := by
  apply LFunction_ne_zero_of_one_le_re _ hs
  exact hpole.imp id (fun h hn => h ((principal_iff M χ).mp hn))

theorem principal_pole_ne_zero : HeckeOrigin.poleRemoved (character M 1) 1 ≠ 0 :=
  HeckeOrigin.poleRemoved_one_ne_zero _ rfl
