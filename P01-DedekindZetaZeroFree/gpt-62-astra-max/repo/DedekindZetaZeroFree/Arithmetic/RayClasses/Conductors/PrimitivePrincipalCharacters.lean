module
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterOperations

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F] {m : Ideal (𝓞 F)}

variable (η : DedekindZetaZeroFree.RayClassCharacter F m) (hprimitive : η.IsPrimitive)
    (hprincipal : η.IsPrincipal)

include hprimitive hprincipal in
theorem primitivePrincipal_modulus_eq_top :
    m = ⊤ := by apply @DedekindZetaZeroFree.LargeSieve.RayOperations.modulus_eq_top_of_primitive_principal <;> assumption

include hprimitive hprincipal in
theorem primitivePrincipal_apply_nonzero
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : η I = 1 := by
  exact hprincipal I hI (by rw [(primitivePrincipal_modulus_eq_top η hprimitive hprincipal), sup_top_eq])

include hprimitive hprincipal in
theorem primitivePrincipal_apply_eq_ite
    (I : Ideal (𝓞 F)) : η I = if I = ⊥ then 0 else 1 := by
  by_cases hI : I = ⊥
  · rw [if_pos hI, hI]
    exact (η.eq_zero_iff' ⊥).mpr (Or.inl rfl)
  · rw [if_neg hI]
    exact primitivePrincipal_apply_nonzero η hprimitive hprincipal I hI

end

end DedekindZetaZeroFree.Hecke
