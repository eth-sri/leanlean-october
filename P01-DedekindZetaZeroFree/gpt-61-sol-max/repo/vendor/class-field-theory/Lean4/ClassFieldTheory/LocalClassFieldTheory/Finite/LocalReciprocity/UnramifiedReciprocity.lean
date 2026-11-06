module

public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Unramified reciprocity

For a finite unramified Galois extension, this module composes the actual norm
quotient with its normalized valuation model, the generator-normalized
Frobenius model of the Galois group, and the canonical equivalence with the
abelianization of that cyclic group.
-/
noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The actual unramified local reciprocity equivalence with target `GaloisGroup`.
The norm-subgroup equality and the Frobenius/ZMod normalization are generated
internally from the preceding source lemmas, not passed as hypotheses. -/
noncomputable def unramifiedLocalReciprocityIsoToGaloisGroup
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] :
    NormQuotient K L ≃* Gal(L / K) :=
  (normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L).trans
    (galoisGroupEquivZModOfUnramifiedValuationNormalized K L).symm

/-- The chosen inverse prime element
maps to the arithmetic Frobenius under the actual reciprocity equivalence. -/
@[simp]
theorem unramifiedLocalReciprocityIsoToGaloisGroup_inverseIntegerRingUniformizerFieldUnit
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] :
    unramifiedLocalReciprocityIsoToGaloisGroup K L
        (normClass K L (inverseIntegerRingUniformizerFieldUnit K)) =
      arithmeticFrobeniusOfUnramifiedValuation K L := by
  unfold unramifiedLocalReciprocityIsoToGaloisGroup
  change (galoisGroupEquivZModOfUnramifiedValuationNormalized K L).symm
      (normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L
        (normClass K L (inverseIntegerRingUniformizerFieldUnit K))) =
    arithmeticFrobeniusOfUnramifiedValuation K L
  rw [normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk]
  rw [LocalClassFieldTheory.valuationModDegreeMulHom_apply,
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
    v_inverseIntegerRingUniformizerFieldUnit]
  simp
  rw [← galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius K L]
  exact (galoisGroupEquivZModOfUnramifiedValuationNormalized K L).symm_apply_apply _


















section
variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] (x : Kˣ)
include K L x in
/-- The actual reciprocity equivalence to
`GaloisGroup` sends any field unit class to the corresponding power of arithmetic
Frobenius, with exponent its normalized valuation. -/
theorem unramifiedLocalReciprocityIsoToGaloisGroup_normClass
      :
    unramifiedLocalReciprocityIsoToGaloisGroup K L (normClass K L x) =
      (arithmeticFrobeniusOfUnramifiedValuation K L) ^
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := by
  unfold unramifiedLocalReciprocityIsoToGaloisGroup
  change (galoisGroupEquivZModOfUnramifiedValuationNormalized K L).symm
      (normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure K L
        (normClass K L x)) =
    (arithmeticFrobeniusOfUnramifiedValuation K L) ^
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)
  rw [normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure_mk]
  rw [LocalClassFieldTheory.valuationModDegreeMulHom_apply]
  rw [← galoisGroupEquivZModOfUnramifiedValuationNormalized_arithmeticFrobenius_zpow K L
    (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x))]
  exact (galoisGroupEquivZModOfUnramifiedValuationNormalized K L).symm_apply_apply _

/-- The actual unramified local reciprocity equivalence with abelianized target.
It composes the valuation quotient and normalized Frobenius model, then
passes to the abelianization of the
cyclic Galois group. -/
noncomputable def unramifiedLocalReciprocityIso
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] :
    NormQuotient K L ≃* Abelianization (Gal(L / K)) :=
  (unramifiedLocalReciprocityIsoToGaloisGroup K L).trans
    (galoisGroupEquivAbelianizationOfUnramifiedValuation K L)

/-- With abelianized target, the chosen
inverse prime element maps to the class of the arithmetic Frobenius. -/
@[simp]
theorem unramifiedLocalReciprocityIso_inverseIntegerRingUniformizerFieldUnit
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] :
    unramifiedLocalReciprocityIso K L
        (normClass K L (inverseIntegerRingUniformizerFieldUnit K)) =
      Abelianization.of (arithmeticFrobeniusOfUnramifiedValuation K L) := by
  unfold unramifiedLocalReciprocityIso
  change galoisGroupEquivAbelianizationOfUnramifiedValuation K L
      (unramifiedLocalReciprocityIsoToGaloisGroup K L
        (normClass K L (inverseIntegerRingUniformizerFieldUnit K))) =
    Abelianization.of (arithmeticFrobeniusOfUnramifiedValuation K L)
  rw [unramifiedLocalReciprocityIsoToGaloisGroup_inverseIntegerRingUniformizerFieldUnit]
  rfl


















include K L x in
/-- The unramified reciprocity map
on a general field unit is the arithmetic Frobenius class raised to the
normalized valuation. -/
theorem unramifiedLocalReciprocityIso_normClass
      :
    unramifiedLocalReciprocityIso K L (normClass K L x) =
      (Abelianization.of (arithmeticFrobeniusOfUnramifiedValuation K L)) ^
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := by
  unfold unramifiedLocalReciprocityIso
  change galoisGroupEquivAbelianizationOfUnramifiedValuation K L
      (unramifiedLocalReciprocityIsoToGaloisGroup K L (normClass K L x)) =
    (Abelianization.of (arithmeticFrobeniusOfUnramifiedValuation K L)) ^
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)
  rw [unramifiedLocalReciprocityIsoToGaloisGroup_normClass]
  rw [galoisGroupEquivAbelianizationOfUnramifiedValuation_apply]
  rw [map_zpow]

/-- The actual unramified Artin map induced by the certificate-free
reciprocity equivalence.  This avoids introducing `LocalReciprocityDataReal`
as an assumption package. -/
noncomputable def unramifiedLocalArtinMap
    (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [IsUnramifiedValuedExtension K L] :
    Kˣ →* Abelianization (Gal(L / K)) :=
  (unramifiedLocalReciprocityIso K L).toMonoidHom.comp (normClass K L)

include K L x in
/-- States the theorem `unramifiedLocalArtinMap_apply`. -/
@[simp]
theorem unramifiedLocalArtinMap_apply
      :
    unramifiedLocalArtinMap K L x =
      unramifiedLocalReciprocityIso K L (normClass K L x) :=
  rfl

include K L x in
/-- In the arithmetic-Frobenius convention,
the actual local Artin map sends `x` to the arithmetic Frobenius class raised
to `v_K(x)`. -/
theorem unramifiedLocalArtinMap_eq_frobenius_zpow
      :
    unramifiedLocalArtinMap K L x =
      (Abelianization.of (arithmeticFrobeniusOfUnramifiedValuation K L)) ^
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x) := by
  rw [unramifiedLocalArtinMap_apply,
    unramifiedLocalReciprocityIso_normClass]
end


end LocalClassFieldTheory

end
