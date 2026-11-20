module

public import ValuedFieldTheory.Ramification.HilbertRamification.UniformizerGradedHom
public import ValuedFieldTheory.Ramification.HilbertRamification.CharacterMap
public import ValuedFieldTheory.Ramification.HilbertRamification.CompleteDVF
public import ValuedFieldTheory.Ramification.HilbertRamification.RamificationCharacterization

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Comparing first principal units in the two ramification conventions

The DVF filtration uses units of the valuation ring, whereas Hilbert's
ramification group uses the principal-unit subgroup of the field units.
This file identifies their first levels before comparing group actions.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification

open ValuationTheory.DiscreteValuationField

variable {L : Type u} [Field L]

end RamificationTheory.HilbertRamification

end
