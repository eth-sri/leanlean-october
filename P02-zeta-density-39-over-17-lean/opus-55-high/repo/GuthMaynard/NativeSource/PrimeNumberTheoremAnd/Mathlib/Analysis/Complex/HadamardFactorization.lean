/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Divisor
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Meromorphic.NormalForm
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Topology.MetricSpace.Annulus

/-!
# The Hadamard quotient

If `f` is entire, nontrivial, and the divisor-indexed canonical product of genus `m` converges,
then there is an entire zero-free function `H` with

`f z = H z * z ^ (ord₀ f) * divisorCanonicalProduct m f univ z`.

The quotient `H` is obtained as the meromorphic normal form of
`f / (z ^ (ord₀ f) * divisorCanonicalProduct ...)`.

The quotient construction here is centered at `0`.  General-center API is derived downstream by
translating the function; see `hadamard_factorization_of_order_centered`.

## Main results

* `exists_entire_nonzero_hadamardQuotient` : existence of `H`
* `hadamardDenom`, `differentiable_hadamardDenom`

Downstream: `HadamardFactorization/Summability` (Jensen counting), `Growth`, and `Order`
assemble the full factorization `hadamard_factorization_of_order`.

## References

* [tao246bComplexAnalysis], Theorem 22 for the finite-order Hadamard factorization strategy
* [boas1954] and [levin1980] for Weierstrass factors, canonical products, and the classical
  Hadamard product theorem
-/

@[expose] public section

namespace Complex.Hadamard

open Filter Topology Set Complex

open scoped BigOperators Topology

/-!
## Boundedness on compact annuli (away from `z₀`)

On any compact set separated from `z₀`, the quotient by `(z - z₀)^k` is bounded.
-/

end Complex.Hadamard
