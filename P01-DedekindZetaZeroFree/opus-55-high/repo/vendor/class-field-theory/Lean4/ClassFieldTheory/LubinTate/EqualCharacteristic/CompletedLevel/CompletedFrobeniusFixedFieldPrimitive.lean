module

public import Mathlib.SetTheory.Cardinal.Finite
public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The completed theta-intertwining theorem: the fixed-field primitive point over the completed base

The direct theta value has the changed completed primitive polynomial as
its minimal polynomial over the completed maximal-unramified Laurent field.
Comparing degrees shows that this point generates the whole completed level.
-/

noncomputable section

open scoped LaurentSeries Polynomial PowerSeries

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance
    equalCharacteristicCompletedFrobeniusFixedFieldCompletedPrimitiveBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  laurentSeriesCoefficientAlgebra

/-- Provides the instance `equalCharacteristicCompletedFrobeniusIdentificationLevelCharP`. -/
instance equalCharacteristicCompletedFrobeniusIdentificationLevelCharP
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic] (n : ℕ) :
    CharP (equalCharacteristicCompletedLevelField F n)
      F.residueCharacteristic :=
  charP_of_injective_algebraMap
    (algebraMap (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n)).injective
    F.residueCharacteristic
