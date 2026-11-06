module

public import Mathlib

public import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence

@[expose] public section


/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# normalization of the equal-characteristic parameter

The Laurent-series valuation sends `T` to `exp (-1)`.  The power-series
description of its integer ring makes `T` a genuine prime element, so the
canonical normalized additive valuation sends `T⁻¹` to `1`.
-/

noncomputable section

open scoped PowerSeries LaurentSeries ValuativeRel WithZero

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

universe u v

variable {K : Type u} [Field K]

section
variable (F : LocalField.{u, v} K)
include F
/-- The explicit Laurent parameter has Laurent-series value `exp (-1)`. -/
theorem equalCharacteristicLaurentUniformizer_laurentValuation
      :
    (Valued.v : Valuation F.residueField⸨X⸩ ℤᵐ⁰)
        (equalCharacteristicLaurentUniformizer F) =
      WithZero.exp (-1) := by
  change (Valued.v : Valuation F.residueField⸨X⸩ ℤᵐ⁰)
      (((PowerSeries.X : F.residueField⟦X⟧))) = _
  simpa using LaurentSeries.valuation_X_pow F.residueField 1

/-- The Laurent parameter in the canonical integer ring determined by the
native Laurent valuation. -/
noncomputable def equalCharacteristicLaurentUniformizerInteger
      :
    letI := equalCharacteristicLaurentValuativeRel F
    (ValuativeRel.valuation F.residueField⸨X⸩).integer := by
  letI  :=
    equalCharacteristicLaurentValuativeRel F
  exact powerSeriesEquivLaurentValuativeInteger F.residueField
    PowerSeries.X












/-- The explicit Laurent parameter is a prime element of the canonical
integer ring. -/
theorem equalCharacteristicLaurentUniformizerInteger_irreducible
      :
    letI := equalCharacteristicLaurentValuativeRel F
    Irreducible (equalCharacteristicLaurentUniformizerInteger F) := by
  let  :=
    equalCharacteristicLaurentValuativeRel F
  change Irreducible
    (powerSeriesEquivLaurentValuativeInteger F.residueField
      PowerSeries.X)
  apply PowerSeries.X_irreducible.map <;> assumption

/-- The Laurent parameter as a nonzero field unit. -/
noncomputable def equalCharacteristicLaurentUniformizerUnit
      : F.residueField⸨X⸩ˣ :=
  Units.mk0 (equalCharacteristicLaurentUniformizer F) (by
    intro hzero
    have hval := equalCharacteristicLaurentUniformizer_laurentValuation F
    rw [hzero, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm)

/-- States the theorem `equalCharacteristicLaurentUniformizerUnit_coe`. -/
@[simp]
theorem equalCharacteristicLaurentUniformizerUnit_coe
      :
    (equalCharacteristicLaurentUniformizerUnit F).1 =
      equalCharacteristicLaurentUniformizer F :=
  rfl

/-- In the normalized additive convention used here, the inverse Laurent
parameter has value one. -/
theorem equalCharacteristicLaurentUniformizerUnit_inv_valuationMap
      :
    letI := equalCharacteristicLaurentValuativeRel F
    letI := equalCharacteristicLaurentIsNonarchimedeanLocalField F
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap F.residueField⸨X⸩
      (Additive.ofMul (equalCharacteristicLaurentUniformizerUnit F)⁻¹) = 1 := by
  let L := F.residueField⸨X⸩
  let : ValuativeRel L := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField L :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply]
  exact LocalFieldTheory.v_integerRingIrreducibleFieldUnit_inv L
    (equalCharacteristicLaurentUniformizerInteger F)
    (equalCharacteristicLaurentUniformizerInteger_irreducible F)
    (equalCharacteristicLaurentUniformizerUnit F) (by
      change equalCharacteristicLaurentUniformizer F =
        equalCharacteristicLaurentUniformizer F
      rfl)
end


end EqualCharacteristic
end LubinTate

end
