module

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
public import Mathlib.NumberTheory.RamificationInertia.Unramified

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/




set_option autoImplicit false

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











namespace IsUnramifiedAtFinitePlaces









variable
    {k : Type u} {K : Type v} {F : Type w}
    [Field k] [NumberField k]
    [Field K] [NumberField K]
    [Field F] [NumberField F]
    [Algebra k K] [Algebra k F] [Algebra K F]
    [IsScalarTower k K F]
























































































































end IsUnramifiedAtFinitePlaces

end
