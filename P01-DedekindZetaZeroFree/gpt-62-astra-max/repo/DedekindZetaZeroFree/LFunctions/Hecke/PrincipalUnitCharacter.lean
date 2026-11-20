module

public import DedekindZetaZeroFree.LFunctions.Hecke.IdealSeriesAndContinuationWitnesses

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

noncomputable section
open scoped NumberField Classical

variable (F : Type) [Field F] [NumberField F]

def principalUnitRayCharacter :
    DedekindZetaZeroFree.RayClassCharacter F (⊤ : Ideal (𝓞 F)) where
  toFun I := if I = ⊥ then 0 else 1
  map_mul' := by
    intro I J
    by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;>
      simp [hI, hJ, Ideal.mul_eq_bot]
  map_top' := by
    have h : (⊤ : Ideal (𝓞 F)) ≠ ⊥ := bot_lt_top.ne'
    simp [h]
  eq_zero_iff' := by
    intro I
    by_cases hI : I = ⊥ <;> simp [hI]
  map_span' := by
    intro α hα _ _
    simp [Ideal.span_singleton_eq_bot, hα]

theorem principalUnitRayCharacter_apply
    (I : Ideal (𝓞 F)) :
    principalUnitRayCharacter F I = if I = ⊥ then 0 else 1 := rfl

@[simp] theorem principalUnitRayCharacter_bot :
    principalUnitRayCharacter F ⊥ = 0 := by
  rw [principalUnitRayCharacter_apply]
  simp

theorem principalUnitRayCharacter_isPrincipal :
    (principalUnitRayCharacter F).IsPrincipal := by
  intro I hI _
  rw [principalUnitRayCharacter_apply]
  simp [hI]

theorem principalUnitRayCharacter_isPrimitive :
    (principalUnitRayCharacter F).IsPrimitive := fun 𝔣 h𝔣 => absurd h𝔣 (not_lt_of_ge le_top)

theorem exists_principalUnitHeckeWitness (hF : NumberField.IsTotallyComplex F) :
    Nonempty (PrincipalHeckeWitness (principalUnitRayCharacter F)) :=
  exists_principalHeckeWitness hF (f := ⊤) bot_lt_top.ne'
    (principalUnitRayCharacter F) (principalUnitRayCharacter_isPrimitive F)
    (principalUnitRayCharacter_isPrincipal F)

end

end DedekindZetaZeroFree.LargeSieve
