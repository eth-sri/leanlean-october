module

public import Mathlib

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section


namespace DedekindZetaZeroFree.Hecke

noncomputable section

open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F] {m : Ideal (𝓞 F)}

section
variable (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (hprimitive : η.IsPrimitive) (hprincipal : η.IsPrincipal)
include η hprimitive hprincipal
theorem primitivePrincipal_modulus_eq_top
      :
    m = ⊤ := by
  by_contra hm
  have hlt : m < ⊤ := lt_top_iff_ne_top.mpr hm
  obtain ⟨α, hα0, _hα1, _hpos, hspan, hne⟩ := hprimitive ⊤ hlt
  have hspanne : Ideal.span {α} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hα0
  exact hne (hprincipal _ hspanne hspan)

theorem primitivePrincipal_apply_nonzero
     
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) : η I = 1 := by
  have hm  := primitivePrincipal_modulus_eq_top η hprimitive hprincipal
  apply hprincipal <;> aesop

theorem primitivePrincipal_apply_eq_ite
     
    (I : Ideal (𝓞 F)) : η I = if I = ⊥ then 0 else 1 := by
  by_cases hI : I = ⊥
  · rw [if_pos hI, hI]
    exact (η.eq_zero_iff' ⊥).mpr (Or.inl rfl)
  · rw [if_neg hI]
    apply primitivePrincipal_apply_nonzero <;> assumption
end


end

end DedekindZetaZeroFree.Hecke
