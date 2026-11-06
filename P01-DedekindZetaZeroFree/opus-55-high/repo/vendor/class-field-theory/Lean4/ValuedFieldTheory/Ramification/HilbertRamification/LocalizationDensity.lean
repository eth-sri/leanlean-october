module

public import ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import ValuedFieldTheory.Valuation.Completion.FiniteLocalization
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
public import ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds
public import ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
public import ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup
public import ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Localization and decomposition comparison through density

For an infinite algebraic extension, the canonical `L_w` is the algebraic
localization `L K_v`, not the whole metric completion.  This file records the
density consequences needed to transport inertia and ramification conditions
between `L` and `L_w`.  None of the results below assumes finite degree.
-/

noncomputable section

universe u v

namespace HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

open AlgebraicNumberTheory.Valuations

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]


namespace ValuationSubring

end ValuationSubring

section Localization

variable (vK : AbsoluteValue K ℝ)
variable (w : AbsoluteValueExtension vK L)

local instance completionAlgebra : Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2
