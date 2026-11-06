/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorIndex
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Convergence and holomorphy of divisor-indexed canonical products

This file proves uniform convergence on compacts, locally uniform convergence, holomorphy, and the
genus-one logarithmic-derivative identity for the divisor-indexed canonical product
`Complex.Hadamard.divisorCanonicalProduct`, under the standard summability hypothesis.

It also provides finiteness lemmas for subsets of the divisor index type cut out by a norm bound.
-/

@[expose] public section

open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set

namespace Complex.Hadamard

/-!
## Finiteness of “small” divisor indices
-/

/-!
## Uniform convergence on compact sets
-/

/-!
## Entire-ness (holomorphy) of the divisor-indexed canonical product
-/

/-!
## Logarithmic derivative of the genus-one divisor product
-/

end Complex.Hadamard
