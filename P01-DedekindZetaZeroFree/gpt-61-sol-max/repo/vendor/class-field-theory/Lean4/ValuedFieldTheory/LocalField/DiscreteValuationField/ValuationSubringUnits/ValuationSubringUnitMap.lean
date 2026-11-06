module

public import Mathlib

public import ValuedFieldTheory.LocalField.DiscreteValuationField.Basic

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/



set_option autoImplicit false

/-!
# Valuation-subring units inside field units

This file defines the canonical homomorphism from units of a complete-DVF
valuation ring to units of its fraction field.
-/

noncomputable section

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField

namespace CompleteDVF

variable {K : Type u} [Field K]

section
variable (F : CompleteDVF.{u, v} K)
include F
/-- The inclusion `O_K^* -> K^*` for the chosen valuation ring of a complete
DVF. -/
noncomputable def valuationSubringUnitsToFieldUnits
       :=
  F.valuation.valuationSubring.unitGroup.subtype.comp
    F.valuation.valuationSubring.unitGroupMulEquiv.symm.toMonoidHom

/--
The defining evaluation formula for `coe_valuationSubringUnitsToFieldUnits` is
`(((CompleteDVF.valuationSubringUnitsToFieldUnits F) a : Kˣ) : K) = (a : F.valuationSubring)`.
-/
@[simp] theorem coe_valuationSubringUnitsToFieldUnits_apply
      (a : F.valuationSubringˣ) :
    (((LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits F) a : Kˣ) : K) =
      (a : F.valuationSubring) := by
  rfl

/--
Establishes the membership statement `(CompleteDVF.valuationSubringUnitsToFieldUnits F) a ∈
F.valuation.valuationSubring.unitGroup`.
-/
theorem valuationSubringUnitsToFieldUnits_mem_unitGroup
      (a : F.valuationSubringˣ) :
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits F) a ∈
      F.valuation.valuationSubring.unitGroup := by
  change
    ((F.valuation.valuationSubring.unitGroupMulEquiv.symm a :
      F.valuation.valuationSubring.unitGroup) : Kˣ) ∈
      F.valuation.valuationSubring.unitGroup
  exact (F.valuation.valuationSubring.unitGroupMulEquiv.symm a).2
end



end CompleteDVF
end LocalFieldTheory.DiscreteValuationField

end
