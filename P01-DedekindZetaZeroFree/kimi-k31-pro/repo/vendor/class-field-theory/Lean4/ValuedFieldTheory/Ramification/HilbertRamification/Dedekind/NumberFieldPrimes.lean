module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.PrimeContractions
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.OrbitCardinality
public import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.TowerInvariants

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Hilbert ramification theory: number-field prime ideals in the fixed fields

This file proves the ramification and inertia invariant statements for the
contracted primes `P_Z` and `P_T` appearing in
the decomposition and inertia fixed-field tower.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open Algebra NumberField
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

variable {K L : Type*}
variable [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]































end Dedekind
end HilbertRamification

end
