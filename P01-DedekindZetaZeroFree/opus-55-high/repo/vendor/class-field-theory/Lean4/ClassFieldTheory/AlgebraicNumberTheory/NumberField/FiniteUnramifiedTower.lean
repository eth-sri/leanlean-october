module

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
public import Mathlib.NumberTheory.RamificationInertia.Unramified

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Finite-prime unramifiedness in towers of number fields

This file records the tower properties of being unramified at every
finite prime.  The transitivity and intermediate-field arguments are
proved from multiplicativity of ramification indices.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

attribute [local instance] Ideal.Quotient.field

universe u v w

/-- A number-field extension is unramified at finite places when every
height-one prime of the top ring of integers is unramified over the
base ring of integers. -/
def IsUnramifiedAtFinitePlaces
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 L),
    Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal

namespace IsUnramifiedAtFinitePlaces
