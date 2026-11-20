module

public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
public import Mathlib.FieldTheory.Galois.Basic
public import ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
public import ValuedFieldTheory.Ramification.Herbrand.Function
public import ValuedFieldTheory.Ramification.HilbertRamification.FiniteGaloisLevelIndependence
public import ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction
public import ValuedFieldTheory.Ramification.HilbertRamification.HerbrandTheorem

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Upper ramification jumps

The actual finite-level upper filtration attached to the canonical
complete-DVF structure of a nonarchimedean local field, together with its
right-limit subgroup and the intrinsic predicate for an upper jump.
-/

noncomputable section

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped ValuativeRel

universe y

namespace LocalFieldTheory

end LocalFieldTheory

namespace RamificationTheory.LocalField

open LocalFieldTheory
open RamificationTheory

end RamificationTheory.LocalField

end
