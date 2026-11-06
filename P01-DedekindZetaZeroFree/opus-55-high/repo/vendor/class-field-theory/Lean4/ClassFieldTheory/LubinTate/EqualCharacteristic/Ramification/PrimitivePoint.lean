module

public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
public import ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
public import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
public import Mathlib.RingTheory.Norm.Basic
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
public import ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness
public import ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# The chosen complete valuation and primitive Lubin--Tate point

This module constructs the actual complete discrete valuation on an explicit
finite equal-characteristic Lubin--Tate level.  It proves that the chosen
primitive point generates the integral closure and is a uniformizer.
-/

noncomputable section

open scoped LaurentSeries Pointwise PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.ValuedExtension
open LubinTate.EqualCharacteristic

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v y

variable {K : Type u} [Field K]

section ChosenRamificationTarget

variable {K₀ : Type} [Field K₀]


section PrimitivePointDisplacementValuation

noncomputable local instance
    equalCharacteristicLubinTateLevelField_finiteDimensional_forDisplacementValuation
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_finiteDimensional F n

noncomputable local instance
    equalCharacteristicLubinTateLevelField_isGalois_forDisplacementValuation
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_isGalois F n
