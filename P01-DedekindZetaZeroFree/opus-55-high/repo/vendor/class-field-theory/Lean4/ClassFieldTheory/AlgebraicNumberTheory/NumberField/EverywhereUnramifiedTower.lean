module

public import ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedTower
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Everywhere-unramified towers of number fields

This file combines finite-prime and infinite-place unramifiedness and
records its tower and intermediate-field properties.
-/

open scoped NumberField

universe u v w

/-- A number-field extension is everywhere unramified when it is
unramified at every finite prime and at every infinite place. -/
structure IsEverywhereUnramified
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop where
  /-- The extension is unramified at every finite prime. -/
  finitePlaces : IsUnramifiedAtFinitePlaces K L
  /-- The extension is unramified at every infinite place. -/
  infinitePlaces : IsUnramifiedAtInfinitePlaces K L

namespace IsEverywhereUnramified
