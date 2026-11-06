/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Basic
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Norm
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Trigonometric
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Exp
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StripBounds
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Pow.Real
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaStripBound

/-!
# Analytic continuation and finite order for the Riemann zeta function

This file gives growth bounds for `completedRiemannZeta₀` (Λ₀) and the removable
extension of `(s - 1)ζ(s)`.

Note: Mathlib distinguishes between:
- `completedRiemannZeta₀` : the entire function Λ₀(s)
- `completedRiemannZeta` : Λ(s) = Λ₀(s) - 1/s - 1/(1-s), which has simple poles at 0 and 1

The key ingredients are:
* Mathlib's `differentiable_completedZeta₀` for entirety of Λ₀
* The functional equation `completedRiemannZeta₀_one_sub`
* Stirling-type bounds for `Complex.Gammaℝ`
* `norm_riemannZeta_le` from `RiemannZetaStripBound` for strip bounds on `ζ`

## Main results

* `completedRiemannZeta₀_order_one` : growth bound implying order at most one for
  `completedRiemannZeta₀`
* `completedRiemannZeta₀_entireOfOrderAtMost_one` (in `RiemannZetaHadamard`) : packaged as
  `Complex.Hadamard.EntireOfOrderAtMost`
* `zeta_minus_pole_entire_growth` : a coarse global bound for the removable extension of
  `(s - 1)ζ(s)`.

## References

* [tao246bComplexAnalysis], Theorem 22 and Exercise 23, for the order-one growth input used in
  the finite-order Hadamard strategy for completed zeta functions
* [titchmarsh1986] and [edwards1974] for the classical completed-zeta and ξ-function growth
  background; the formalized object here is the additive pole-removal `Λ₀`, not Riemann's `ξ`

## Tags

Riemann zeta function, completed zeta function, finite order, Hadamard factorization
-/

@[expose] public section

open Complex Set Filter Topology Metric
open scoped Real

namespace Complex

/-! ### Finite order of the completed zeta function -/

end Complex
