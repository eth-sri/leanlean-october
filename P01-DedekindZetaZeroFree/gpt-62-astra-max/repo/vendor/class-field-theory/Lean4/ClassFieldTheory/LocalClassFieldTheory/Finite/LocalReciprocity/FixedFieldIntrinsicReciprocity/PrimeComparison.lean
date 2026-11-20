module

public import Mathlib.FieldTheory.Galois.Basic
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeComparison
public import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.IntrinsicFrobeniusFixedField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Intrinsic fixed-field prime comparison

This module compares intrinsic local Artin maps with the ambient fixed-field norm-residue symbol.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

section IntrinsicFixedFieldPrimeComparison

variable
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      Gal(SeparableClosure K / K))
    (J : ClosedSubgroup Gal(SeparableClosure K / K))
    (hJH : J.toSubgroup ≤ H.field.toSubgroup)
    [hJnormal : (extensionSubgroup H.field J hJH).Normal]
    [hJfinite : Finite
      (H.field.toSubgroup ⧸ extensionSubgroup H.field J hJH)]
    (e : intrinsicFixedFieldSeparableClosureEquiv K H)

local notation "F" =>
  abstractFixedField K (SeparableClosure K) H.field

local notation "E" =>
  abstractRelativeFixedField K (SeparableClosure K) hJH

local notation "iFE" =>
  e.symm.toAlgHom.comp
    (IntermediateField.val
      (abstractRelativeFixedField
        K (SeparableClosure K) hJH))

local notation "EI" =>
  finiteGaloisAbstractExtensionOfEmbedding F E iFE

local notation "RF" =>
  FiniteAbstractField.toFiniteResidueAbstractField
    (intrinsicFiniteAbstractBase F)
    (localResidueDatum F)

local notation "RH" =>
  FiniteAbstractField.toFiniteResidueAbstractField
    H (localResidueDatum K)

local notation "qF" =>
  finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E iFE

local notation "qH" =>
  abstractExtensionQuotientEquivGaloisGroup
    K (SeparableClosure K) H.field J hJH hJnormal

local instance intrinsicPrimeComparison_separableClosureAlgebra :
    Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).algebra

local instance intrinsicPrimeComparison_absoluteFinite :
    Finite
      ((baseField
        Gal(SeparableClosure K / K)).toSubgroup ⧸
        extensionSubgroup
          (baseField Gal(SeparableClosure K / K))
          H.field (le_baseField H.field)) :=
  H.finite

local instance intrinsicPrimeComparison_fixedFieldFiniteDimensional :
    FiniteDimensional K F :=
  abstractFixedField_finiteDimensional
    K (SeparableClosure K) H.field H.finite

local instance intrinsicPrimeComparison_fixedFieldNormed :
    NontriviallyNormedField F :=
  finiteExtensionSpectralNormedField K F

local instance intrinsicPrimeComparison_fixedFieldValuative :
    ValuativeRel F :=
  finiteExtensionSpectralValuativeRel K F

local instance intrinsicPrimeComparison_fixedFieldLocal :
    IsNonarchimedeanLocalField F :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K F

local instance intrinsicPrimeComparison_extensionFiniteDimensional :
    FiniteDimensional F E :=
  abstractRelativeFixedField_finiteDimensional
    K (SeparableClosure K) H.field J hJH H.finite hJfinite

local instance intrinsicPrimeComparison_extensionGalois :
    IsGalois F E :=
  abstractRelativeFixedField_isGalois
    K (SeparableClosure K) H.field J hJH hJnormal

local instance intrinsicPrimeComparison_extensionNormal :
    (extensionSubgroup
      (intrinsicAbstractBase F) (EI).field (EI).below).Normal :=
  (EI).normal

local instance intrinsicPrimeComparison_extensionFinite :
    Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) (EI).field (EI).below) :=
  (EI).finite

local instance intrinsicPrimeComparison_residueExtensionFinite :
    Finite
      ((RF).field.toSubgroup ⧸
        extensionSubgroup (RF).field (EI).field (EI).below) := by
  exact intrinsicPrimeComparison_extensionFinite K H J hJH e

/-- The local Artin homomorphism of the actual finite fixed-field extension,
using the canonical local structure constructed from the original field. -/
noncomputable def intrinsicFixedFieldLocalArtinMonoidHom :
    Additive Fˣ →+ Additive (Abelianization Gal(E / F)) :=
  MonoidHom.toAdditive (localArtinMonoidHom F E)

/-- The concrete norm-residue symbol of the intrinsic finite extension,
evaluated at a unit of the finite fixed field. -/
noncomputable def intrinsicFixedFieldConcreteSymbolValue
    (x : Fˣ) : Abelianization Gal(E / F) :=
  concreteNormResidueSymbolOfEmbedding
    F E iFE
    (localResidueDatum F)
    (localHenselianValuation F)
    (separableClosureUnits_isClassFormation F) x

/-- Map an intrinsic extension-quotient class to the abelianization of the
intrinsic finite-extension Galois group. -/
def intrinsicFixedFieldSourceFrobeniusAbelianization
    (q : (EI).extensionQuotient) :
    Abelianization Gal(E / F) :=
  Abelianization.of (qF q)

section

variable (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e)

/-- The intrinsic closed subgroup fixed by the Frobenius element associated to
the finite fixed-field extension. -/
abbrev intrinsicFixedFieldFrobeniusSourceClosedField :=
  (localResidueDatum F).frobeniusFixedField
    RF (EI).field (EI).below σ

/-- The intrinsic Frobenius-fixed closed subgroup lies below the intrinsic
absolute-base subgroup. -/
theorem intrinsicFixedFieldFrobeniusSourceBelow :
    (intrinsicFixedFieldFrobeniusSourceClosedField
        K H J hJH e σ).toSubgroup ≤
      (intrinsicAbstractBase F).toSubgroup :=
  (localResidueDatum F).frobeniusFixedField_le
    RF (EI).field (EI).below σ

/-- The intrinsic abstract fixed field cut out by the intrinsic
Frobenius-fixed closed subgroup. -/
abbrev intrinsicFixedFieldFrobeniusSourceField :=
  abstractFixedField F (SeparableClosure F)
    (intrinsicFixedFieldFrobeniusSourceClosedField
      K H J hJH e σ)

/-- The ambient Frobenius-fixed closed subgroup obtained after transporting
the intrinsic Frobenius element. -/
abbrev intrinsicFixedFieldFrobeniusAmbientClosedField :=
  (localResidueDatum K).frobeniusFixedField
    RH J hJH
    (intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ)

/-- The transported ambient Frobenius-fixed subgroup lies below the ambient
finite fixed subgroup. -/
theorem intrinsicFixedFieldFrobeniusAmbientBelow :
    (intrinsicFixedFieldFrobeniusAmbientClosedField
        K H J hJH e σ).toSubgroup ≤ H.field.toSubgroup :=
  (localResidueDatum K).frobeniusFixedField_le
    RH J hJH
    (intrinsicFrobeniusElementToAmbientFixedField
      K H J hJH e σ)

/-- The ambient relative fixed field cut out by the transported
Frobenius-fixed subgroup. -/
abbrev intrinsicFixedFieldFrobeniusAmbientField :=
  abstractRelativeFixedField K (SeparableClosure K)
    (intrinsicFixedFieldFrobeniusAmbientBelow
      K H J hJH e σ)

end

local instance intrinsicPrimeComparison_frobeniusSourceAlgebra
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Algebra F
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ) :=
  (intrinsicFixedFieldFrobeniusSourceField
    K H J hJH e σ).algebra

local instance intrinsicPrimeComparison_frobeniusSourceFiniteDimensional
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    @FiniteDimensional F
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ)
      _ _
      (@Algebra.toModule F
        (intrinsicFixedFieldFrobeniusSourceField
          K H J hJH e σ)
        _ _
        (intrinsicPrimeComparison_frobeniusSourceAlgebra
          K H J hJH e σ)) := by
  let :=
    intrinsicPrimeComparison_frobeniusSourceAlgebra
      K H J hJH e σ
  exact
    @abstractFixedField_finiteDimensional
      F (SeparableClosure F) _ _ inferInstance inferInstance
      (intrinsicFixedFieldFrobeniusSourceClosedField
        K H J hJH e σ)
      ((localResidueDatum F).frobeniusFixedField_absoluteFinite
        (intrinsicFiniteAbstractBase F) (EI).field (EI).below σ)

local instance intrinsicPrimeComparison_frobeniusSourceNormed
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    NontriviallyNormedField
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ) :=
  finiteExtensionSpectralNormedField F
    (intrinsicFixedFieldFrobeniusSourceField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusSourceValuative
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    ValuativeRel
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ) :=
  finiteExtensionSpectralValuativeRel F
    (intrinsicFixedFieldFrobeniusSourceField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusSourceLocal
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    IsNonarchimedeanLocalField
      (intrinsicFixedFieldFrobeniusSourceField
        K H J hJH e σ) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField F
    (intrinsicFixedFieldFrobeniusSourceField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusSourceValuationExtension
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Valuation.HasExtension
      (ValuativeRel.valuation F)
      (ValuativeRel.valuation
        (intrinsicFixedFieldFrobeniusSourceField
          K H J hJH e σ)) :=
  finiteExtensionSpectralValuation_hasExtension F
    (intrinsicFixedFieldFrobeniusSourceField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusAmbientAlgebraK
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Algebra K
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  (abstractFixedField K (SeparableClosure K)
    (intrinsicFixedFieldFrobeniusAmbientClosedField
      K H J hJH e σ)).algebra

local instance intrinsicPrimeComparison_frobeniusAmbientAlgebraF
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Algebra F
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  (intrinsicFixedFieldFrobeniusAmbientField
    K H J hJH e σ).algebra

local instance intrinsicPrimeComparison_frobeniusAmbientFiniteDimensionalK
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    @FiniteDimensional K
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ)
      _ _
      (@Algebra.toModule K
        (intrinsicFixedFieldFrobeniusAmbientField
          K H J hJH e σ)
        _ _
        (intrinsicPrimeComparison_frobeniusAmbientAlgebraK
          K H J hJH e σ)) := by
  let :=
    intrinsicPrimeComparison_frobeniusAmbientAlgebraK
      K H J hJH e σ
  exact
    abstractFixedField_finiteDimensional
      K (SeparableClosure K)
      (intrinsicFixedFieldFrobeniusAmbientClosedField
        K H J hJH e σ)
      ((localResidueDatum K).frobeniusFixedField_absoluteFinite
        H J hJH
        (intrinsicFrobeniusElementToAmbientFixedField
          K H J hJH e σ))

local instance intrinsicPrimeComparison_frobeniusAmbientNormed
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    NontriviallyNormedField
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  finiteExtensionSpectralNormedField K
    (intrinsicFixedFieldFrobeniusAmbientField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusAmbientValuative
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    ValuativeRel
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  finiteExtensionSpectralValuativeRel K
    (intrinsicFixedFieldFrobeniusAmbientField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusAmbientLocal
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    IsNonarchimedeanLocalField
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  finiteExtensionSpectralIsNonarchimedeanLocalField K
    (intrinsicFixedFieldFrobeniusAmbientField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusAmbientValuationExtension
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Valuation.HasExtension
      (ValuativeRel.valuation K)
      (ValuativeRel.valuation
        (intrinsicFixedFieldFrobeniusAmbientField
          K H J hJH e σ)) :=
  finiteExtensionSpectralValuation_hasExtension K
    (intrinsicFixedFieldFrobeniusAmbientField
      K H J hJH e σ)

local instance intrinsicPrimeComparison_frobeniusAmbientFiniteDimensionalF
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    @FiniteDimensional F
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ)
      _ _
      (@Algebra.toModule F
        (intrinsicFixedFieldFrobeniusAmbientField
          K H J hJH e σ)
        _ _
        (intrinsicPrimeComparison_frobeniusAmbientAlgebraF
          K H J hJH e σ)) := by
  let :=
    intrinsicPrimeComparison_frobeniusAmbientAlgebraF
      K H J hJH e σ
  exact
    abstractRelativeFixedField_finiteDimensional
      K (SeparableClosure K) H.field
      (intrinsicFixedFieldFrobeniusAmbientClosedField
        K H J hJH e σ)
      (intrinsicFixedFieldFrobeniusAmbientBelow
        K H J hJH e σ)
      H.finite
      ((localResidueDatum K).frobeniusFixedField_finite
        RH J hJH
        (intrinsicFrobeniusElementToAmbientFixedField
          K H J hJH e σ))

local instance intrinsicPrimeComparison_frobeniusAmbientSeparable
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Algebra.IsSeparable K
      (intrinsicFixedFieldFrobeniusAmbientField
        K H J hJH e σ) :=
  by
    change Algebra.IsSeparable K
      (abstractFixedField K (SeparableClosure K)
        (intrinsicFixedFieldFrobeniusAmbientClosedField
          K H J hJH e σ))
    infer_instance

local instance intrinsicPrimeComparison_frobeniusSourceQuotientFinite
    (σ : intrinsicFixedFieldFrobeniusElements K H J hJH e) :
    Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F)
          (intrinsicFixedFieldFrobeniusSourceClosedField
            K H J hJH e σ)
          (intrinsicFixedFieldFrobeniusSourceBelow
            K H J hJH e σ)) := by
  exact
    (localResidueDatum F).frobeniusFixedField_finite
      RF (EI).field (EI).below σ

end IntrinsicFixedFieldPrimeComparison

end LocalClassFieldTheory

end
