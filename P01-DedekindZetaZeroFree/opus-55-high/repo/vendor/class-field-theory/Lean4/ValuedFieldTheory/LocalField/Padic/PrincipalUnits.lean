module

public import ValuedFieldTheory.Valuation.LocalRingEquiv
public import ValuedFieldTheory.LocalField.Analytic.PrincipalUnitExpLogEquiv
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UniformizerPrincipalQuotient
public import ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.NumberTheory.Padics.ProperSpace

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Principal units of the p-adic field

This file identifies the standard p-adic integer and complete-DVF models,
computes their principal-unit quotients, and records the logarithm/exponential
power formulas used by local cyclotomic norm calculations.
-/

noncomputable section

open scoped ValuativeRel WithZero

namespace LocalFieldTheory.Padic

open LocalFieldTheory
open ValuationTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (p : ℕ) [Fact p.Prime]

/-- The residue field of the canonical p-adic discrete valuation is finite. -/
instance padicDVR_residueField_finite :
    Finite (IsLocalRing.ResidueField
      (LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p).valuationSubring) := by
  simpa [LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF,
    ValuationTheory.DiscreteValuationField.CompleteDVF.residueField,
    ValuationTheory.DiscreteValuationField.CompleteDVF.valuationSubring,
    ValuationTheory.DiscreteValuationField.CompleteDVF.toDVF] using
      LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_finite p

/-- The canonical multiplicative discrete valuation sends `p` to
`exp (-1)`. -/
theorem padicDVR_valuation_p :
    LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation p (p : ℚ_[p]) =
      WithZero.exp (-1 : ℤ) := by apply LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicDVRValuation_apply_p <;> assumption
