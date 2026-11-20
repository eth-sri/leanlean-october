module

public import ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Reduction
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.RationalFixedFieldBaseChange

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Fixed-field instance spine for rational finite-norm transport

This leaf names the finite-dimensional, scalar-tower, number-field, Galois,
and quotient instances reused by the rational finite-norm transport modules.
The public dependent type aliases are compiled once here.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open CyclicCohomology

section RationalIdeleExtension

open Reciprocity
open LocalClassFieldTheory

namespace RationalFiniteNormTransferInternal

/-- Shared commutativity proof for ordinary idèle class groups. -/
theorem ideleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

local instance
    fieldSpineIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ideleClassGroupIsMulCommutative

/-- Shared normality proof for subgroups of ordinary idèle class groups. -/
theorem ideleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  N.normal_of_isMulCommutative

local instance
    fieldSpineIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  ideleClassSubgroupNormal N

/-- The canonical absolute algebra structure on a rational relative fixed field. -/
@[reducible] noncomputable def absoluteAlgebra
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Algebra ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
  inferInstance

/-- The finite-dimensional structure on a rational abstract fixed field. -/
theorem fixedFiniteDimensional
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K hKfinite

section

variable (K L : ClosedSubgroup (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)

/-- The relative finite-dimensional structure on the fixed-field extension
attached to an inclusion of closed subgroups. -/
theorem relativeFiniteDimensional
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite

/-- The canonical scalar tower on a rational relative fixed field. -/
theorem relativeScalarTower :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- Absolute finite-dimensionality of a rational relative fixed field. -/
theorem relativeAbsoluteFiniteDimensional
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let := fixedFiniteDimensional K
  let := relativeFiniteDimensional K L hLK
  let := relativeScalarTower K L hLK
  exact FiniteDimensional.trans ℚ F E

end

/-- The number-field structure on a rational abstract fixed field. -/
alias fixedNumberField := GlobalClassFieldTheory.Reciprocity.rationalNormQuotientAbstractFixedFieldNumberField

/-- The number-field structure on a rational relative fixed field. -/
alias relativeNumberField := GlobalClassFieldTheory.Reciprocity.rationalNormQuotientAbstractRelativeFixedFieldNumberField

/-- The Galois structure on a normal rational relative fixed field. -/
theorem relativeIsGalois
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ) K L hLK hnormal

end RationalFiniteNormTransferInternal

local instance
    fieldSpinePublicIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  RationalFiniteNormTransferInternal.ideleClassGroupIsMulCommutative

local instance
    fieldSpinePublicIdeleClassSubgroupNormal
    {F : Type} [Field F] [NumberField F]
    (N : Subgroup (IdeleClassGroup F)) : N.Normal :=
  RationalFiniteNormTransferInternal.ideleClassSubgroupNormal N

/-- The fixed-field idele-class type used as the domain of rational
finite-norm transport. -/
noncomputable abbrev rationalFiniteNormTransferBaseIdeleClass
    (K : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional K
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField K
  IdeleClassGroup F

/-- The additive ordinary idele-class norm quotient used as the target of
rational finite-norm transport. -/
noncomputable abbrev rationalFiniteNormTransferQuotientTarget
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] : Type :=
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional K
  letI : FiniteDimensional F E :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      K L hLK
  letI : IsScalarTower ℚ F E :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      K L hLK
  letI : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      K L hLK
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField K
  letI : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      K L hLK
  letI : IsGalois F E :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      K L hLK hnormal
  Additive (IdeleClassGroup F ⧸ (_root_.ideleClassNorm F E).range)

namespace RationalFiniteNormTransferInternal

/-- The canonical additive zero on the named finite-norm transfer target.
Naming this instance prevents repeated typeclass reduction of the dependent
fixed-field quotient. -/
@[reducible] noncomputable def quotientTargetZero
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Zero (rationalFiniteNormTransferQuotientTarget
      K L hLK hnormal) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  letI : FiniteDimensional ℚ F :=
    RationalFiniteNormTransferInternal.fixedFiniteDimensional K
  letI : FiniteDimensional F E :=
    RationalFiniteNormTransferInternal.relativeFiniteDimensional
      K L hLK
  letI : IsScalarTower ℚ F E :=
    RationalFiniteNormTransferInternal.relativeScalarTower
      K L hLK
  letI : FiniteDimensional ℚ E :=
    RationalFiniteNormTransferInternal.relativeAbsoluteFiniteDimensional
      K L hLK
  letI : NumberField F :=
    RationalFiniteNormTransferInternal.fixedNumberField K
  letI : NumberField E :=
    RationalFiniteNormTransferInternal.relativeNumberField
      K L hLK
  letI : IsGalois F E :=
    RationalFiniteNormTransferInternal.relativeIsGalois
      K L hLK hnormal
  exact inferInstanceAs
    (Zero (Additive
      (IdeleClassGroup F ⧸ (_root_.ideleClassNorm F E).range)))

end RationalFiniteNormTransferInternal

end RationalIdeleExtension

end IdealClassFieldTheory
end GlobalClassFieldTheory

end
