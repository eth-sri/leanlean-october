module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterFiniteOrder
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.QuadraticExtensionRealizationData
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.QuadraticArtinCharacter
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.FinitePrimeClassCompatibility
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.QuadraticCharacterDescent
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassSubgroupExistence

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem exists_quadraticRayExtensionData
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (f : Ideal (𝓞 F)) (hf : f ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F f)
    (hq : ∀ I : Ideal (𝓞 F), η I ^ 3 = η I)
    (hn : ¬η.IsPrincipal) : Nonempty (QuadraticRayExtensionData η) := by
  let m := RayBridge.fullModulus f hf
  let ψ := RayBridge.descendedCharacter f hf η
  obtain ⟨R⟩ := ClassFieldTheory.rayClassSubgroup_existence F m ψ.ker
  obtain ⟨χ, hinj, hsqχ, hagree, hdeg⟩ :=
    quadraticCharacter_of_rayClassRealization m ψ (RayBridge.descendedCharacter_square f hf η hq) (RayBridge.descendedCharacter_ne_one f hf η hn) R
  exact ⟨{
    extension := R.extension
    character := χ
    degree_two := hdeg
    character_injective := hinj
    character_square := hsqχ
    unramified := fun p hp => R.unramifiedOutsideModulus.1 p
        ((RayBridge.prime_not_mem_fullModulus_support_iff f hf p).2 hp)
    frobenius := by
      intro p hp Q hQ
      rw [← (R.artin_frobenius p ((RayBridge.prime_not_mem_fullModulus_support_iff f hf p).2 hp) Q hQ), hagree]
      exact RayBridge.descendedCharacter_apply_finitePrime f hf η p hp }⟩

end DedekindZetaZeroFree.LargeSieve
