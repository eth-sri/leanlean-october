module

public import ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldCorrespondence
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertNormCharacterization
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldNaturality
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTower
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Conjugation of the small Hilbert class-field tower

For a finite abelian tower, conjugation by the lower base carries the
relative norm subgroup of the upper extension to the relative norm subgroup
of the conjugate extension.  In the rational absolute idele-class formation,
the subgroup defining the small Hilbert class field is intrinsic under the
corresponding automorphism of its actual fixed field.  Finite abelian
classification therefore identifies every conjugate of the second small
Hilbert class field with the original field.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation KummerTheory
open GlobalClassFields LocalClassFieldTheory Reciprocity

section AbstractConjugation

variable
    {G : IntegralRepGroupType}
    [Group G] [TopologicalSpace G] [ContinuousMul G]

 noncomputable def rebaseFiniteAbelianSubextension
    {K K' : ClosedSubgroup G} (h : K = K')
    (L : FiniteAbelianSubextension K) :
    FiniteAbelianSubextension K' :=
  h ▸ L

omit [ContinuousMul G] in
@[simp]
private theorem rebaseFiniteAbelianSubextension_field
    {K K' : ClosedSubgroup G} (h : K = K')
    (L : FiniteAbelianSubextension K) :
    (rebaseFiniteAbelianSubextension h L).field = L.field := by
  cases h
  rfl

 noncomputable def rebaseFixedCodomainHom
    (A : Rep ℤ G)
    {X : Type*} [AddGroup X]
    {K K' : ClosedSubgroup G} (h : K = K')
    (f : X →+ ambientFixedAddSubgroup A K) :
    X →+
      ambientFixedAddSubgroup A K' := by
  cases h
  exact f

omit [ContinuousMul G] in
@[simp]
private theorem rebaseFixedCodomainHom_coe
    (A : Rep ℤ G)
    {X : Type*} [AddGroup X]
    {K K' : ClosedSubgroup G} (h : K = K')
    (f : X →+ ambientFixedAddSubgroup A K)
    (a : X) :
    ((rebaseFixedCodomainHom A h f a :
      ambientFixedAddSubgroup A K') : A.V) =
      (f a : A.V) := by
  cases h
  rfl

end AbstractConjugation

section RationalSmallHilbert

local instance smallHilbertTowerBaseQuotientFinite
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K.field (le_baseField K.field)) :=
  K.finite

local instance smallHilbertTowerRelativeQuotientFinite
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    Finite
      (K.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          K.field L.field L.below) :=
  L.finite

noncomputable local instance smallHilbertTowerBaseFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K.field K.finite

noncomputable local instance smallHilbertTowerRelativeFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below K.finite L.finite

local instance smallHilbertTowerScalarTower
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance smallHilbertTowerAbsoluteFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance smallHilbertTowerBaseNumberField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)

noncomputable local instance smallHilbertTowerRelativeNumberField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance smallHilbertTowerRelativeIsGalois
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below L.normal

end RationalSmallHilbert

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
