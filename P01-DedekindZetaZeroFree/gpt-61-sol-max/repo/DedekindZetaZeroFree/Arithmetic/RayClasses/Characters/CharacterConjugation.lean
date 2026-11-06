module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section


namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped NumberField

variable {F : Type} [Field F] [NumberField F] {m : Ideal (𝓞 F)}

section
variable (η : DedekindZetaZeroFree.RayClassCharacter F m)
include η
def conjugateRayCharacter   :
    DedekindZetaZeroFree.RayClassCharacter F m where
  toFun I := (starRingEnd ℂ) (η I)
  map_mul' := by
    intro I J
    simp only [η.map_mul', map_mul]
  map_top' := by
    simp only [η.map_top', map_one]
  eq_zero_iff' := by
    intro I
    simpa using η.eq_zero_iff' I
  map_span' := by
    intro α hα hm hpos
    simp only [η.map_span' α hα hm hpos, map_one]

@[simp] theorem conjugateRayCharacter_apply
      (I : Ideal (𝓞 F)) :
    conjugateRayCharacter η I = (starRingEnd ℂ) (η I) := rfl







@[simp] theorem conjugateRayCharacter_isPrincipal_iff
      :
    (conjugateRayCharacter η).IsPrincipal ↔ η.IsPrincipal := by
  simp [DedekindZetaZeroFree.RayClassCharacter.IsPrincipal,
    map_eq_one_iff (starRingEnd ℂ) (star_injective)]

@[simp] def rayClassCharacter_apply_bot
       := (η.eq_zero_iff' ⊥).mpr (Or.inl rfl)
end


end

end DedekindZetaZeroFree.Hecke
