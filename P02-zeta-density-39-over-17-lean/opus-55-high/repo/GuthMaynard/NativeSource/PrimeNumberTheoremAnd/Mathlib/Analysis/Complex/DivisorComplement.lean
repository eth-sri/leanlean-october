/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorConvergence
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorFiber

/-!
# Fiber/complement splitting for divisor-indexed partial products

This file defines finitary “partial products” of Weierstrass factors indexed by the divisor, and
develops the corresponding fiber/complement splitting. It also defines the complement canonical
product (replacing fiber factors by `1`) and proves its convergence/holomorphy properties.
-/

@[expose] public section

open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Complement factors

For a fixed point `z₀`, the complement factor agrees with the usual Weierstrass factor away from
the fiber over `z₀`, and is `1` on that fiber.
-/

/-!
## Partial products as a named function

These finite products are the approximants to the divisor-indexed canonical product.
-/

/-!
## Splitting finite partial products into fiber vs complement

This is the finitary “fiber × complement” split.
-/

/-!
## Complement canonical product (fiber factors removed)

For a fixed point `z₀`, one often wants to split the infinite product into a finite “fiber part”
(`val = z₀`, accounting for the multiplicity) and an infinite “complement part” (all other indices).

The complement product is written as a total product by inserting the neutral element `1` on the
fiber indices.
-/

/-!
## Convergence/holomorphy of the complement canonical product

This is the same M-test argument as for `divisorCanonicalProduct`, but with finitely many factors
replaced by `1`. We keep the same summability hypothesis.
-/

end Complex.Hadamard
