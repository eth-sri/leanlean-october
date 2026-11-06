module

public import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.Core
public import ValuedFieldTheory.LocalField.DiscreteValuationField.Basic

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

/-!
# Real-index steps for equal-characteristic Lubin--Tate levels

This file packages the ceiling behavior of the chosen real lower filtration
and the integral values of its inverse Herbrand function.  Together they show
that, on the positive range covered by an explicit finite Lubin--Tate level,
the real upper filtration is constant on the natural-ceiling steps.
-/

noncomputable section

open scoped LaurentSeries

namespace LubinTate

open LubinTate.EqualCharacteristic
open LocalFieldTheory.DiscreteValuationField
open RamificationTheory.HilbertRamification.Higher

universe v

variable {K₀ : Type} [Field K₀]

/-- Finite-dimensionality for explicit levels while forming the real-index
Herbrand functions in this module. -/
noncomputable local instance
    equalCharacteristicLubinTateLevelField_finiteDimensional_forRealIndexSteps
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_finiteDimensional F n

/-- Galoisness for explicit levels while forming the real-index Herbrand
functions in this module. -/
noncomputable local instance
    equalCharacteristicLubinTateLevelField_isGalois_forRealIndexSteps
    (F : LocalField.{0, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) :
    IsGalois F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
  equalCharacteristicLubinTateLevelField_isGalois F n











end LubinTate

end
