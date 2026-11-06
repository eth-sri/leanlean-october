module

public import ClassFieldTheory.LocalFieldTheory.Padic.Cyclotomic.Unramified.CanonicalExtension
public import ValuedFieldTheory.Ramification.HilbertRamification.InertiaRamificationCard
public import ClassFieldTheory.RamificationTheory.HilbertRamification.PadicCyclotomicRamificationIndexBound
public import ClassFieldTheory.RamificationTheory.RamificationIndexComparison

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/






set_option autoImplicit false

/-!
# Canonical p-adic inertia bounds

This file identifies the inertia cardinality of the canonical valuation on a
finite Galois extension of `ℚ_p` with the intrinsic value-group ramification
index, then applies the prime-power cyclotomic ramification bound.
-/

noncomputable section

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

attribute [local instance] Ideal.Quotient.field





end HilbertRamification

end
