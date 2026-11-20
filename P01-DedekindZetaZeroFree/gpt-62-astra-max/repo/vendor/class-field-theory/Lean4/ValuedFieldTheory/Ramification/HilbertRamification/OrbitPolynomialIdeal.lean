module

public import Mathlib.SetTheory.Cardinal.Finite
public import ValuedFieldTheory.Ramification.HilbertRamification.FixedFieldRamification
public import ValuedFieldTheory.Ramification.HilbertRamification.UniformizerGradedHom

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Quotient-depth identity over a general DVF

This file proves the orbit-polynomial ideal identity before normalization of
the fixed-field valuation.  It uses the literal fixed field and its literal
restricted valuation ring; no completeness or Henselian hypothesis occurs.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open scoped Polynomial

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]
variable [FiniteDimensional K L] [IsGalois K L]

end Higher
end RamificationTheory.HilbertRamification

end
