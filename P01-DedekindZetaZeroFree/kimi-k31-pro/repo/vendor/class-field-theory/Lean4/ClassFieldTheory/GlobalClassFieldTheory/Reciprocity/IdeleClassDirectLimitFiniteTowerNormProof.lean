module

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormStatement

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Proof of ordinary norm comparison in finite towers of rational fixed fields

This proof leaf installs the canonical finite-tower context once and splits
the normal-closure embedding calculation, the pointwise coset action, and the
finite product calculation into separate commands.  The public theorem is a
thin wrapper around those providers.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology
open FiniteTowerNormCore

section RationalFiniteTower

variable
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hKfinite : Finite (rationalFixedFieldAbsoluteQuotient K)]
    [hfinite : Finite
      (rationalFixedFieldRelativeQuotient K L hLK)]

local notation "F₀" =>
  abstractFixedField ℚ (SeparableClosure ℚ) K
local notation "E₀" =>
  abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
local notation "N₀" =>
  IntermediateField.normalClosure F₀ E₀ (SeparableClosure ℚ)
 abbrev rationalFiniteTowerRestrictedNormal :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  IntermediateField.restrictScalars ℚ N₀
 abbrev rationalFiniteTowerRestrictedUpper :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  IntermediateField.restrictScalars ℚ E₀
local notation "EQ₀" =>
  rationalFiniteTowerRestrictedUpper K L hLK
local notation "NQ₀" =>
  rationalFiniteTowerRestrictedNormal K L hLK
local notation "U₀" => rationalNormalClosure NQ₀
local notation "Q₀" =>
  K.toSubgroup ⧸ extensionSubgroup K L hLK

noncomputable local instance rationalFiniteTowerLowerFiniteDimensional :
    FiniteDimensional ℚ F₀ :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K hKfinite

noncomputable local instance rationalFiniteTowerUpperFiniteDimensional :
    FiniteDimensional F₀ E₀ :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite

local instance rationalFiniteTowerLowerUpperScalarTower :
    IsScalarTower ℚ F₀ E₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance rationalFiniteTowerUpperAbsoluteFiniteDimensional :
    FiniteDimensional ℚ E₀ :=
  FiniteDimensional.trans ℚ F₀ E₀

noncomputable local instance rationalFiniteTowerRestrictedUpperFiniteDimensional :
    FiniteDimensional ℚ EQ₀ := by
  change FiniteDimensional ℚ E₀
  infer_instance

noncomputable local instance rationalFiniteTowerLowerNumberField :
    NumberField F₀ :=
  NumberField.of_module_finite ℚ F₀

noncomputable local instance rationalFiniteTowerUpperNumberField :
    NumberField E₀ :=
  NumberField.of_module_finite ℚ E₀

local instance rationalFiniteTowerUpperSeparableClosureScalarTower :
    IsScalarTower F₀ E₀ (SeparableClosure ℚ) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

omit hKfinite hfinite in
private theorem rationalFiniteTower_lower_le_upper :
    F₀ ≤ IntermediateField.restrictScalars ℚ E₀ :=
  abstractFixedField_le ℚ (SeparableClosure ℚ) hLK

omit hKfinite hfinite in
private theorem rationalFiniteTower_upper_le_normal :
    IntermediateField.restrictScalars ℚ E₀ ≤ NQ₀ := by
  intro x hx
  exact IntermediateField.le_normalClosure E₀ hx

omit hKfinite hfinite in
private theorem rationalFiniteTower_lower_le_normal :
    F₀ ≤ NQ₀ :=
  (rationalFiniteTower_lower_le_upper K L hLK).trans
    (rationalFiniteTower_upper_le_normal K L hLK)

local instance rationalFiniteTowerNormalScalarTower :
    IsScalarTower ℚ F₀ N₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance rationalFiniteTowerNormalFiniteDimensional :
    FiniteDimensional F₀ N₀ :=
  normalClosure.is_finiteDimensional F₀ E₀ (SeparableClosure ℚ)

noncomputable local instance rationalFiniteTowerNormalAbsoluteFiniteDimensional :
    FiniteDimensional ℚ N₀ :=
  FiniteDimensional.trans ℚ F₀ N₀

noncomputable local instance rationalFiniteTowerNormalNumberField :
    NumberField N₀ :=
  NumberField.of_module_finite ℚ N₀

noncomputable local instance rationalFiniteTowerRestrictedNormalFiniteDimensional :
    FiniteDimensional ℚ NQ₀ := by
  change FiniteDimensional ℚ N₀
  infer_instance

 theorem rationalFiniteTower_normal_le_rationalNormalClosure :
    NQ₀ ≤ (U₀ : IntermediateField ℚ (SeparableClosure ℚ)) := by
  change NQ₀ ≤ IntermediateField.normalClosure
    ℚ NQ₀ (SeparableClosure ℚ)
  exact IntermediateField.le_normalClosure NQ₀

 theorem rationalFiniteTower_lower_le_rationalNormalClosure :
    F₀ ≤ (U₀ : IntermediateField ℚ (SeparableClosure ℚ)) :=
  (rationalFiniteTower_lower_le_normal K L hLK).trans
    (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)

 theorem rationalFiniteTower_upper_le_rationalNormalClosure :
    IntermediateField.restrictScalars ℚ E₀ ≤
      (U₀ : IntermediateField ℚ (SeparableClosure ℚ)) :=
  (rationalFiniteTower_upper_le_normal K L hLK).trans
    (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)

local instance rationalFiniteTowerRationalNormalClosureLowerAlgebra :
    Algebra F₀ U₀ :=
  (IntermediateField.inclusion
    (rationalFiniteTower_lower_le_rationalNormalClosure K L hLK)).toRingHom.toAlgebra

local instance rationalFiniteTowerRationalNormalClosureUpperAlgebra :
    Algebra E₀ U₀ :=
  (IntermediateField.inclusion
    (rationalFiniteTower_upper_le_rationalNormalClosure K L hLK)).toRingHom.toAlgebra

local instance rationalFiniteTowerRationalNormalClosureNormalAlgebra :
    Algebra N₀ U₀ :=
  (IntermediateField.inclusion
    (rationalFiniteTower_normal_le_rationalNormalClosure K L hLK)).toRingHom.toAlgebra

local instance rationalFiniteTowerRationalNormalClosureLowerScalarTower :
    IsScalarTower ℚ F₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

local instance rationalFiniteTowerRationalNormalClosureUpperScalarTower :
    IsScalarTower ℚ E₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

local instance rationalFiniteTowerRationalNormalClosureNormalScalarTower :
    IsScalarTower ℚ N₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

local instance rationalFiniteTowerLowerUpperClosureScalarTower :
    IsScalarTower F₀ E₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

local instance rationalFiniteTowerLowerNormalClosureScalarTower :
    IsScalarTower F₀ N₀ U₀ :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

local instance rationalFiniteTowerClosureSeparableClosureScalarTower :
    IsScalarTower F₀ U₀ (SeparableClosure ℚ) :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    rfl)

noncomputable local instance rationalFiniteTowerClosureOverUpperFiniteDimensional :
    FiniteDimensional E₀ U₀ :=
  FiniteDimensional.right ℚ E₀ U₀

noncomputable local instance rationalFiniteTowerClosureOverLowerFiniteDimensional :
    FiniteDimensional F₀ U₀ :=
  FiniteDimensional.right ℚ F₀ U₀

noncomputable local instance rationalFiniteTowerClosureOverNormalFiniteDimensional :
    FiniteDimensional N₀ U₀ :=
  FiniteDimensional.right ℚ N₀ U₀

local instance rationalFiniteTowerLowerSeparableClosureGalois :
    IsGalois F₀ (SeparableClosure ℚ) :=
  IsGalois.tower_top_of_isGalois ℚ F₀ (SeparableClosure ℚ)

local instance rationalFiniteTowerNormalGalois : IsGalois F₀ N₀ :=
  IsGalois.normalClosure F₀ E₀ (SeparableClosure ℚ)

local instance rationalFiniteTowerClosureOverLowerGalois : IsGalois F₀ U₀ :=
  IsGalois.tower_top_of_isGalois ℚ F₀ U₀

local instance rationalFiniteTowerClosureOverNormalGalois : IsGalois N₀ U₀ :=
  IsGalois.tower_top_of_isGalois ℚ N₀ U₀

noncomputable local instance rationalFiniteTowerQuotientFintype : Fintype Q₀ :=
  Fintype.ofFinite Q₀

 

 

 

 

 

 

































end RationalFiniteTower

end Reciprocity
end GlobalClassFieldTheory

end
