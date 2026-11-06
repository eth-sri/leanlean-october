module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.NumberFieldPrimes

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/





set_option autoImplicit false

/-!
# Global cyclotomic inertia argument: the inertia-generated fixed field is unramified

This file records the ramification-theoretic step in the proof of the global
Kronecker--Weber theorem.  If a subgroup of a finite Galois group contains
the inertia group at every prime of the top field, then its fixed field is
unramified at every finite prime.
-/

noncomputable section

namespace HilbertRamification.Dedekind

open NumberField
open scoped NumberField

attribute [local instance] Ideal.Quotient.field

variable {G M : Type*}
variable [Group G]
variable [Field M] [NumberField M]
variable [MulSemiringAction G M]
variable [IsGaloisGroup G ℚ M]



end HilbertRamification.Dedekind

end
