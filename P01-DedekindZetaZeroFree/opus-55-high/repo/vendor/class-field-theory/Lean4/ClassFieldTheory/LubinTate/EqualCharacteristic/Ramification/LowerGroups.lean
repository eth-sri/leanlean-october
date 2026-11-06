module

public import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.PrimitivePoint
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Finset.Max
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ValuedFieldTheory.Valuation.HenselLemma
public import ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.FieldTheory.Galois.Basic
public import ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.GaloisValuation.Ramification
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Topology.Order.MonotoneContinuity
public import ValuedFieldTheory.Ramification.Herbrand.Tower

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Lower ramification groups of equal-characteristic Lubin--Tate levels

This module identifies the actual lower ramification groups attached to the
chosen complete valuation, both by visible unit-parameter coefficients and by
their exact cardinalities.
-/

noncomputable section

open scoped LaurentSeries Pointwise PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LubinTate.EqualCharacteristic

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v y

variable {K : Type u} [Field K]

section ChosenRamificationTarget

variable {K₀ : Type} [Field K₀]

/-- Finite-dimensionality for the explicit level while computing its lower
ramification groups. -/
noncomputable local instance
    equalCharacteristicLubinTateLevelField_finiteDimensional_forLowerGroups
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_finiteDimensional F n

/-- Galoisness for the explicit level while computing its lower
ramification groups. -/
noncomputable local instance
    equalCharacteristicLubinTateLevelField_isGalois_forLowerGroups
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_isGalois F n
