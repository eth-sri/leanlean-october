/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.FromNumbers
public import ThreeSumApsp.Util.Asymptotics.SoftOSqrtPow
public import ThreeSumApsp.TacticsShort

/-!
# Theorem 21(a), the reduction of Chan and He: inputs of absolute value at most n ^ κ

From n integers bounded by a power of n, the reduction after [CH20, Theorem 5.1] computes
polylogarithmically many arrays of length Õ(n), in Õ(n^{3/2}) time.  This file puts `n ^ κ` for the
bound `U` on the input and proves the three bounds, the last one for the count `scanPairs` in place
of a running time.

* The numbers have `Lam (2 n^κ) = O(log n)` binary digits (`Lam_pow_le`).  So the bound `mPar` on
  the primes is `√n` times a polylogarithm (`softO_mPar`).
* The reduction is correct (`threeSum_iff_exists_convolution3SUM`), there are at most `numBound κ n`
  instances (`length_instances_pow_le`) with entries of absolute value at most `120 n^κ + 40`
  (`abs_instances_pow_le`), and the searches look at no more than `workBound κ n` pairs
  (`scanPairs_pow_le`).
* `numBound κ n` is a polylogarithm, the length `lenOf κ n` of the instances is `n` times a
  polylogarithm, and `workBound κ n` is `n^{3/2}` times a polylogarithm (`isPowPolylog_numBound`,
  `isPowPolylog_lenOf`, `isPowPolylog_workBound`).  These three bounds and `softO_mPar` follow the
  definitions of the parameters through the calculus `SoftOSqrtPow`.
-/

public section

namespace ThreeSumApsp

namespace ChanHe

open Finset

/-! ## The parameters -/

/-- The number of binary digits is a polylogarithm. -/
theorem softO_Lam (κ : ℕ) : SoftOSqrtPow (fun n => Lam (2 * n ^ κ)) 0 := by
  unfold Lam
  growth_sqrt []

/-- The number of primes that we want to choose from is `√n` times a polylogarithm. -/
theorem softO_wPar (κ : ℕ) : SoftOSqrtPow (fun n => wPar n (2 * n ^ κ) + 1) 1 := by
  unfold wPar
  growth_sqrt [softO_Lam κ]

/-- **The bound on the primes is `√n` times a polylogarithm.** -/
theorem softO_mPar (κ : ℕ) : SoftOSqrtPow (fun n => mPar n (2 * n ^ κ)) 1 := by
  unfold mPar
  growth_sqrt [softO_wPar κ]

/-- The instances are not empty arrays. -/
theorem one_le_lenOf (κ n : ℕ) : 1 ≤ lenOf κ n :=
  Nat.succ_le_of_lt (by unfold lenOf mPar; positivity)

/-! ## Correctness, the number of instances, their entries, and the count for the searches -/

section input

variable {κ n : ℕ} {x : Fin n → ℤ}

/-- `Convolution3SUM` on the first `N` cells of an array `y : ℕ → ℤ` is the problem
`ConvOne N y`. -/
theorem convolution3SUM_iff_convOne (N : ℕ) (y : ℕ → ℤ) :
    Convolution3SUM (fun i : Fin N => y i) ↔ ConvOne N y :=
  ⟨fun ⟨i, j, h, e⟩ => ⟨i, j, h, e⟩, fun ⟨u, v, h, e⟩ => ⟨⟨u, by omega⟩, ⟨v, by omega⟩, h, e⟩⟩

end input

/-! ## The three bounds in asymptotic form -/

/-- The length of the instances is `n` times a polylogarithm. -/
theorem isPowPolylog_lenOf (κ : ℕ) : IsPowPolylog (fun n => (lenOf κ n : ℝ)) 1 :=
  SoftOSqrtPow.isPowPolylog (i := 2) (by unfold lenOf; growth_sqrt [softO_mPar κ]) tac_norm_num

end ChanHe

end ThreeSumApsp