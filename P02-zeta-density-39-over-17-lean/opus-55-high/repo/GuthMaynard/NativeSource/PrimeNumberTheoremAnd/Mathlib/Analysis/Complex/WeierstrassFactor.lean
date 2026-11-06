/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Weierstrass elementary factors

We define the Weierstrass elementary factors
`E_m(z) = (1 - z) * exp (∑_{k=1}^m z^k / k)` (as `Complex.weierstrassFactor`) and prove basic
properties and estimates

## Main definitions

* `Complex.partialLogSum m z`: the truncation of `-log (1 - z)`, defined via `Complex.logTaylor`
* `Complex.logTail m z`: the tail `∑_{k>m} z^k / k` as a `tsum` starting at `m + 1`
* `Complex.weierstrassFactor m z`: the elementary factor `E_m(z)`

## Main results

* `Complex.weierstrassFactor_sub_one_pow_bound`: `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)` for `‖z‖ ≤ 1 / 2`
* `Complex.weierstrassFactor_eq_exp_neg_tail`: on `‖z‖ < 1` with `z ≠ 1`,
  `E_m z = exp (-logTail m z)`
* `Complex.norm_partialLogSum_le_nat_mul_max_one_norm_pow`: a crude bound on the truncated
  logarithm series
* `Complex.log_norm_weierstrassFactor_ge_log_norm_one_sub_nat_mul_max_one_norm_pow`: a crude lower
  bound for `log ‖E_m(z)‖` used in minimum-modulus arguments
-/

public section

noncomputable section

open Set

namespace Complex

/-! ## The Weierstrass factor -/

/-! ## Power bound -/

/-!
## Lower bounds on `Real.log ‖weierstrassFactor m z‖`

Auxiliary inequalities for minimum-modulus / Cartan-type arguments in Hadamard factorization.
-/

/-! ## Locally uniform convergence of products of scaled factors -/

end Complex
