module

public import ValuedFieldTheory.LocalField.Padic.Cyclotomic.Unramified.ArithmeticFrobenius
public import ValuedFieldTheory.LocalField.Unramified.RamificationIndexTower
public import ValuedFieldTheory.LocalField.Unramified.Definitions
public import ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
public import ValuedFieldTheory.Valuation.AbsoluteValue.ExponentialValuation
public import ValuedFieldTheory.Valuation.Henselian.Complete
public import ValuedFieldTheory.Valuation.LocalRingEquiv
public import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# The canonical valuation on the unramified extension of `ℚ_p`

The unramified cyclotomic construction is proved for the additive exponential
valuation.  This file identifies that presentation, for
`ℚ_[p]`, with the concrete complete-DVF valuation used by the local class
field theory files.  It also specializes the least-exponent degree formula
to roots of unity of order `p ^ f - 1`.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open scoped WithZero

end Valuations
end AlgebraicNumberTheory

end
