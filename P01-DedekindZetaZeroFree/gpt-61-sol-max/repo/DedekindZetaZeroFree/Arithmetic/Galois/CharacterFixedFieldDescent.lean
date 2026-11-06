module

public import Mathlib

public import DedekindZetaZeroFree.LFunctions.Hecke.PrimeArtinValues

@[expose] public section


namespace DedekindZetaZeroFree.AbelianQuotient

open scoped NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L]

section
variable (ρ : ComplexDual (L ≃ₐ[K] L))
include ρ
noncomputable def characterFixedField    :=
  IntermediateField.fixedField ρ.ker

noncomputable abbrev characterFixedFieldRestriction   :
    (L ≃ₐ[K] L) →* ((characterFixedField ρ) ≃ₐ[K] (characterFixedField ρ)) :=
  AlgEquiv.restrictNormalHom (characterFixedField ρ) (F := K) (K₁ := L)

theorem characterFixedFieldRestriction_ker   :
    (characterFixedFieldRestriction ρ).ker = ρ.ker := by
  rw [characterFixedFieldRestriction, IntermediateField.restrictNormalHom_ker]
  exact IntermediateField.fixingSubgroup_fixedField ρ.ker

noncomputable def characterOnFixedField   :
    ComplexDual ((characterFixedField ρ) ≃ₐ[K] (characterFixedField ρ)) :=
  (QuotientGroup.kerLift ρ).comp (IsGalois.normalAutEquivQuotient ρ.ker).symm.toMonoidHom

theorem characterOnFixedField_comp_restriction   :
    (characterOnFixedField ρ).comp (characterFixedFieldRestriction ρ) = ρ := by
  apply MonoidHom.ext
  intro σ
  dsimp only [characterOnFixedField, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  change QuotientGroup.kerLift ρ ((IsGalois.normalAutEquivQuotient ρ.ker).symm
    ((AlgEquiv.restrictNormalHom (IntermediateField.fixedField ρ.ker)
      (F := K) (K₁ := L)) σ)) = ρ σ
  rw [← IsGalois.normalAutEquivQuotient_apply ρ.ker σ, MulEquiv.symm_apply_apply]
  rfl

theorem characterOnFixedField_ne_one   (hρ : ρ ≠ 1) :
    characterOnFixedField ρ ≠ 1 := by
  intro h
  apply hρ
  rw [← characterOnFixedField_comp_restriction ρ, h]
  rfl
end


end DedekindZetaZeroFree.AbelianQuotient
