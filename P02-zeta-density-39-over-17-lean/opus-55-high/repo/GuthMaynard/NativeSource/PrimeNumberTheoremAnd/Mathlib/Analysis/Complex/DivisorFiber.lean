/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorUnits
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Analytic.Order

/-!
# Fibers of the divisor index type

This file studies the fiber `{p : divisorZeroIndex₀ f univ | divisorZeroIndex₀_val p = z₀}`.
It provides a canonical `Finset` for this fiber and identifies its cardinality with the divisor
multiplicity and (for holomorphic functions) with `analyticOrderNatAt`.
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology BigOperators

namespace Complex.Hadamard

/-!
## Divisor values vs analytic order (holomorphic functions)
-/

/-!
## The multiplicity fiber is finite and has the expected cardinality
-/

end Complex.Hadamard
