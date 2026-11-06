module

public import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.LowerGroups
public import ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.GaloisAction
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.PrimitivePoint
public import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.DisplacementValuation

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/







set_option autoImplicit false

/-!
# Herbrand function and upper ramification groups of Lubin--Tate levels

The lower-group calculation is integrated here to compute the actual Herbrand
function and the resulting upper ramification groups of the chosen
equal-characteristic Lubin--Tate level.
-/

noncomputable section

open scoped LaurentSeries Pointwise PowerSeries

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LubinTate.EqualCharacteristic
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v y

variable {K : Type u} [Field K]

section ChosenRamificationTarget

variable {K₀ : Type} [Field K₀]

attribute [local instance]
  equalCharacteristicLubinTateLevelField_finiteDimensional_forLowerGroups
  equalCharacteristicLubinTateLevelField_isGalois_forLowerGroups

 

 



 


















end ChosenRamificationTarget

end LubinTate

end
