module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterDescent
public import DedekindZetaZeroFree.Arithmetic.LocalFields.UnramifiedInertiaCriterion
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassFieldReciprocity
public import DedekindZetaZeroFree.LFunctions.Hecke.PrimeArtinValues
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

open scoped NumberField
open IsDedekindDomain UniqueFactorizationMonoid

namespace DedekindZetaZeroFree.HeckeCorollary

open AbelianQuotient

variable (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) (χ : RayClassCharacter K m)

theorem rayCharacter_eq_zero_of_mem_modulus_support
    (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ (narrowIdealModulus K m hm).finitePart.support) :
    χ p.asIdeal = 0 := by
  apply (χ.eq_zero_iff' p.asIdeal).mpr
  exact Or.inr (by simpa only [sup_eq_left.mpr (((Ideal.mem_normalizedFactors_iff hm).mp (Multiset.count_ne_zero.mp (by
    simpa using Finsupp.mem_support_iff.mp hp))).2)] using p.isPrime.ne_top)

theorem rayCharacter_galoisRealization
    (R : ClassFieldTheory.RayClassFieldRealization K (narrowIdealModulus K m hm)) :
    ∃ ρ : ComplexDual (R.extension ≃ₐ[K] R.extension),
      (ρ = 1 ↔ χ.IsPrincipal) ∧
      ∀ (p : HeightOneSpectrum (𝓞 K))
        (_hp : p ∉ (narrowIdealModulus K m hm).finitePart.support)
        (W : HeightOneSpectrum (𝓞 R.extension)),
        W.asIdeal.LiesOver p.asIdeal →
          χ p.asIdeal = primeArtinValue ρ W := by
  obtain ⟨ψ, hψ, hprincipal⟩ := rayCharacterDescent K m hm χ
  let ρ :=
    ψ.toHomUnits.comp R.artinEquiv.symm.toMonoidHom
  refine ⟨ρ, ?_, ?_⟩
  · constructor
    · intro hρ
      apply hprincipal.mpr
      apply MonoidHom.ext
      intro c
      simpa [ρ] using (congrArg (fun z : ℂˣ ↦ (z : ℂ)) (DFunLike.congr_fun hρ (R.artinEquiv c)))
    · intro hχ
      apply MonoidHom.ext
      intro σ
      apply Units.ext
      simp [ρ, (hprincipal.mp hχ)]
  · intro p hp W hW
    rw [primeArtinValue, ((unramifiedIffInertiaBot p W hW).mp (R.unramifiedOutsideModulus.1 p hp W.asIdeal W.isPrime hW)), ite_eq_left bot_le]
    rw [hψ, rayIdealClass_of_finitePrime K m hm p hp]
    change ψ (ClassFieldTheory.rayClassOfFinitePrime _ p hp) =
      (ψ.toHomUnits (R.artinEquiv.symm
        (ClassFieldTheory.arithmeticFrobeniusAt W)) : ℂ)
    rw [← R.artin_frobenius p hp W hW, R.artinEquiv.symm_apply_apply]
    rfl

theorem exists_rayCharacter_galoisRealization :
    ∃ R : ClassFieldTheory.RayClassFieldRealization K (narrowIdealModulus K m hm),
    ∃ ρ : ComplexDual (R.extension ≃ₐ[K] R.extension),
      (ρ = 1 ↔ χ.IsPrincipal) ∧
      ∀ (p : HeightOneSpectrum (𝓞 K))
        (_hp : p ∉ (narrowIdealModulus K m hm).finitePart.support)
        (W : HeightOneSpectrum (𝓞 R.extension)),
        W.asIdeal.LiesOver p.asIdeal →
          χ p.asIdeal = primeArtinValue ρ W := by
  obtain ⟨R⟩ := ClassFieldTheory.rayClassField_reciprocity K (narrowIdealModulus K m hm)
  exact ⟨R, rayCharacter_galoisRealization K m hm χ R⟩

end DedekindZetaZeroFree.HeckeCorollary
