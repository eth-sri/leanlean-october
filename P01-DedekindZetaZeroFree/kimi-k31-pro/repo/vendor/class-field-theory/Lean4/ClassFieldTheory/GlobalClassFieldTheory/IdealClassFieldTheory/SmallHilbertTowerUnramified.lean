module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldMaximalSubextension
public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.SmallHilbertTowerRealization
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationSubextension
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAbstractFixedField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Unramifiedness of the two-stage small Hilbert tower

The second-stage class field is selected in the rational absolute class
formation.  This file transports its exact abstract norm subgroup back
to the ordinary idele class group of the actual middle fixed field.
The intrinsic small-Hilbert characterization then proves genuine
unramifiedness at both finite and infinite places.
-/

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation
open KummerTheory
open LocalClassFieldTheory
open GlobalClassFields

/-- Transitivity over a number field, with the relative module fixed by
the given algebra before the concrete fixed-field carriers are inserted. -/
 theorem smallHilbertTowerAbsoluteFiniteDimensionalOfRelative
    (F N : Type) [Field F] [NumberField F] [Field N]
    [Algebra ℚ N] [Algebra F N] [IsScalarTower ℚ F N]
    [FiniteDimensional F N] :
    FiniteDimensional ℚ N :=
  FiniteDimensional.trans ℚ F N

section SelectedTower

variable (K : Type) [Field K] [NumberField K]

/-- The actual top field in the selected two-stage small Hilbert
tower, viewed over the selected first small Hilbert class field. -/
abbrev smallHilbertTowerTopField :=
  abstractRelativeFixedField ℚ (SeparableClosure ℚ)
    (smallHilbertTowerSecondSubextension K).below

 noncomputable abbrev smallHilbertTowerFirstStageFiniteAbstractField :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :=
  let K₀ :=
    Reciprocity.numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  { field := L.field
    finite := by
      let : Finite
          ((baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
            CyclicCohomology.extensionSubgroup
              (baseField
                (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
              K₀.field (le_baseField K₀.field)) :=
        K₀.finite
      let : Finite
          (K₀.field.toSubgroup ⧸
            CyclicCohomology.extensionSubgroup
              K₀.field L.field L.below) :=
        L.finite
      exact
        FiniteGaloisSubextension.finite_extension_trans
          L.below (le_baseField K₀.field) }

 noncomputable instance
    smallHilbertTowerFirstStageAbsoluteQuotientFinite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          (smallHilbertClassFieldSubextension K).field
          (le_baseField
            (smallHilbertClassFieldSubextension K).field)) :=
  (smallHilbertTowerFirstStageFiniteAbstractField K).finite

/-- The relative algebra is the canonical algebra carried by the
intermediate-field presentation of the selected top field. -/
@[reducible]
 noncomputable instance
    smallHilbertTowerTopAlgebra :
    Algebra
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  (smallHilbertTowerTopField K).algebra

/-- Freeze the scalar-action owner induced by the canonical relative
algebra. -/
@[reducible]
 noncomputable def
    smallHilbertTowerTopSMul :
    SMul
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  Algebra.toSMul (self := smallHilbertTowerTopAlgebra K)

/-- Freeze the module owner induced by the same canonical relative
algebra. -/
@[reducible]
 noncomputable def
    smallHilbertTowerTopModule :
    Module
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  @Algebra.toModule
    (smallHilbertClassField K)
    (smallHilbertTowerTopField K)
    _ _
    (smallHilbertTowerTopAlgebra K)

section

attribute [local instance] smallHilbertTowerTopModule

/-- The second selected stage is finite-dimensional over the first
small Hilbert class field. -/
noncomputable instance smallHilbertTowerTopFiniteDimensional :
    FiniteDimensional
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldFiniteDimensional
    (smallHilbertTowerSecondSubextension K)

end

/-- The rational base, first small Hilbert class field, and second
selected stage form the actual scalar tower. -/
noncomputable instance smallHilbertTowerTopScalarTower :
    IsScalarTower ℚ
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- The selected second stage is a finite extension of the rational
field. -/
noncomputable instance smallHilbertTowerTopAbsoluteFiniteDimensional :
    FiniteDimensional ℚ (smallHilbertTowerTopField K) :=
  smallHilbertTowerAbsoluteFiniteDimensionalOfRelative
    (smallHilbertClassField K)
    (smallHilbertTowerTopField K)

/-- The selected second-stage fixed field is a number field. -/
noncomputable instance smallHilbertTowerTopNumberField :
    NumberField (smallHilbertTowerTopField K) :=
  NumberField.of_module_finite ℚ (smallHilbertTowerTopField K)

/-- The selected second stage is an abelian Galois extension of the
first small Hilbert class field. -/
noncomputable instance smallHilbertTowerTopIsAbelianGalois :
    IsAbelianGalois
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois
    (smallHilbertTowerSecondSubextension K)

end SelectedTower

/-- The actual norm range from the selected second stage is exactly
the intrinsic small-Hilbert subgroup of the first stage. -/
@[simp]
theorem smallHilbertTowerSecondStage_ideleClassNorm_range
    (K : Type) [Field K] [NumberField K] :
    (_root_.ideleClassNorm
      (smallHilbertClassField K)
      (smallHilbertTowerTopField K)).range =
        smallHilbertClassFieldNormSubgroup
          (K := smallHilbertClassField K) := by
  let K₀ :=
    Reciprocity.numberFieldTowerFiniteAbstractField K
      (smallHilbertClassFieldNormAmbient K)
  let L := smallHilbertClassFieldSubextension K
  let F := abstractFixedField ℚ (SeparableClosure ℚ) L.field
  let T :=
    abstractRelativeFixedField ℚ (SeparableClosure ℚ)
      (secondSmallHilbertClassFieldSubextension K₀ L).below
  have hFType : (F : Type) = smallHilbertClassField K := by
    rfl
  have hTType : (T : Type) = (smallHilbertTowerTopField K : Type) := by
    rfl
  cases hFType
  cases hTType
  exact secondSmallHilbertClassFieldSubextension_ideleClassNorm_range K₀ L





end IdealClassFieldTheory
end GlobalClassFieldTheory

end
