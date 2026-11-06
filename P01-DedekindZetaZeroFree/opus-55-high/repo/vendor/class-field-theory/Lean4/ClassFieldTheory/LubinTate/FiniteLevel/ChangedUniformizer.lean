module

public import ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates
public import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNorm
public import Mathlib.RingTheory.Valuation.Extension
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.UniformizerIntegerValuation
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
public import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction
public import ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Unit changes of a standard Lubin--Tate uniformizer

For a local field `F`, a chosen uniformizer `π`, and a valuation-ring unit
`u`, the product `uπ` is again a uniformizer.  Consequently all of the
standard finite-level Lubin--Tate constructions are available for `uπ`.

This file packages that elementary, characteristic-independent part of the
changed-uniformizer norm argument.  In particular, the negative primitive
generator at the changed level has norm `uπ`.  It also records the
cancellation step saying that, inside the norm subgroup of the original
`π`-level, membership of `uπ` is equivalent to membership of `u`, since `π`
is already a norm.

The remaining comparison between the `π`-level and the `uπ`-level requires
an actual finite-level intertwining equivalence; no such equivalence is
assumed here.
-/

noncomputable section

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The unit change `uπ` of a chosen integral uniformizer. -/
def standardLubinTateChangedUniformizer
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (u : F.valuationSubringˣ) :
    F.valuationSubring :=
  (u : F.valuationSubring) * π

/-- The changed parameter is literally the unit factor times the original
uniformizer. -/
theorem standardLubinTateChangedUniformizer_eq_unit_mul
    (F : LocalField.{u, v} K) (π : F.valuationSubring)
    (u : F.valuationSubringˣ) :
    standardLubinTateChangedUniformizer F π u =
      (u : F.valuationSubring) * π :=
  rfl

/-- Multiplication by a valuation-ring unit preserves the uniformizer
property. -/
theorem standardLubinTateChangedUniformizer_isUniformizer
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    F.toCompleteDVF.valuation.IsUniformizer
      (standardLubinTateChangedUniformizer F π u : K) := 
  hπ.of_associated
    (associated_unit_mul_right π (u : F.valuationSubring) u.isUnit)

/-- The standard finite Lubin--Tate level attached to the changed
uniformizer `uπ`. -/
abbrev standardLubinTateChangedLevelField
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :=
  standardLubinTateLevelField
    (standardLubinTateChangedUniformizer_isUniformizer hπ u) n

/-- The chosen primitive generator of the changed standard level. -/
abbrev standardLubinTateChangedLevelGenerator
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    standardLubinTateChangedLevelField hπ u n :=
  standardLubinTateLevelGenerator
    (standardLubinTateChangedUniformizer_isUniformizer hπ u) n

/-- A valuation-ring unit regarded as a unit of the base field. -/
def standardLubinTateUnitFactorFieldUnit
    (F : LocalField.{u, v} K) (u : F.valuationSubringˣ) :
    Kˣ :=
  CompleteDVF.valuationSubringUnitsToFieldUnits F.toCompleteDVF u

/-- The unit-factor inclusion has the expected underlying field element. -/
@[simp]
theorem standardLubinTateUnitFactorFieldUnit_coe
    (F : LocalField.{u, v} K) (u : F.valuationSubringˣ) :
    (standardLubinTateUnitFactorFieldUnit F u : K) =
      (u : F.valuationSubring) := 
  CompleteDVF.coe_valuationSubringUnitsToFieldUnits_apply
    F.toCompleteDVF u

/-- The changed uniformizer, regarded as a nonzero base-field unit. -/
def standardLubinTateChangedUniformizerUnit
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    Kˣ :=
  standardLubinTateBaseUniformizerUnit
    (standardLubinTateChangedUniformizer_isUniformizer hπ u)

/-- The changed uniformizer unit has underlying field element `uπ`. -/
@[simp]
theorem standardLubinTateChangedUniformizerUnit_coe
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    (standardLubinTateChangedUniformizerUnit hπ u : K) =
      (standardLubinTateChangedUniformizer F π u : K) := 
  standardLubinTateBaseUniformizerUnit_coe
    (standardLubinTateChangedUniformizer_isUniformizer hπ u)

/-- In the base-field unit group, the changed uniformizer is the product
of the included valuation-ring unit and the original uniformizer. -/
theorem standardLubinTateChangedUniformizerUnit_eq_unit_mul
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) :
    standardLubinTateChangedUniformizerUnit hπ u =
      standardLubinTateUnitFactorFieldUnit F u *
        standardLubinTateBaseUniformizerUnit hπ := by
  apply Units.ext
  rfl

/-- The negative primitive generator at the changed level has norm `uπ`. -/
theorem standardLubinTateChanged_norm_neg_levelGenerator
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (u : F.valuationSubringˣ) (n : ℕ) :
    Algebra.norm K
        (-standardLubinTateChangedLevelGenerator hπ u n) =
      (standardLubinTateChangedUniformizer F π u : K) :=
  standardLubinTate_norm_neg_levelGenerator
    (standardLubinTateChangedUniformizer_isUniformizer hπ u) n
