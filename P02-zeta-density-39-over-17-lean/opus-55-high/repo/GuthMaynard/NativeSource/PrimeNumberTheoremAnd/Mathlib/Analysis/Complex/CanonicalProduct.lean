/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.WeierstrassFactor

/-!
# Canonical products

This file defines canonical products attached to a sequence `a : ℕ → ℂ`:

`canonicalProduct m a z := ∏' n, weierstrassFactor m (z / a n)`.

The convergence results specialize the locally uniform product API for scaled Weierstrass factors
developed in `Mathlib.Analysis.Complex.WeierstrassFactor`.
-/

@[expose] public section

noncomputable section

open Filter Topology

namespace Complex

end Complex
