module

public import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# The completed theta-intertwining theorem: normalization of a changed Laurent uniformizer

The parameter `aT`, with `a` a power-series unit, is a prime element of the
canonical Laurent integer ring.  Consequently its inverse has normalized
additive value one.  This is the concrete prime certificate used in the
changed-level norm argument.
-/

noncomputable section

open scoped PowerSeries LaurentSeries ValuativeRel WithZero

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]







































/-- The changed Laurent parameter as a nonzero field unit. -/
noncomputable def equalCharacteristicChangedLaurentUniformizerUnit
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    F.residueField⸨X⸩ˣ :=
  Units.mk0 (equalCharacteristicChangedLaurentUniformizer F a)
    (equalCharacteristicChangedLaurentUniformizer_ne_zero F a)

/-- States the theorem `equalCharacteristicChangedLaurentUniformizerUnit_coe`. -/
@[simp]
theorem equalCharacteristicChangedLaurentUniformizerUnit_coe
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicChangedLaurentUniformizerUnit F a).1 =
      equalCharacteristicChangedLaurentUniformizer F a :=
  rfl






















end EqualCharacteristic
end LubinTate

end
