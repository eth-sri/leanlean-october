/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Time

/-!
# 3SUM from Convolution-3SUM: the memory map of core; specifications of params, prep, core

Theorem 21(a), after [CH20, Theorem 5.1].  core decides 3SUM with a solver
of Convolution-3SUM.  It first calls params, which computes the three parameters of the reduction,
and prep, which fills the arrays that the rest of core works on.  The arrays stand one after the
other from a base address `b`.  This file fixes their layout (`Map`) and the specifications of
params, prep and core.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

/-- params(n, V, out) writes `Lam V`, `mPar n V` and `fuel n` to the three cells from `out`. -/
def ParamsSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ (d n V out : ℕ) (μ : ℕ → ℤ), out + 3 ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    ((8 * (mPar n V + 1) ^ 2 + 8 * V + 4 * n + 64 : ℕ) : ℤ) ≤ lim.word → d + 1 ≤ lim.depth →
    Meets lim P p d [n, V, out] μ (tParams n V) fun _ μ' =>
      Seg μ' out [(Lam V : ℤ), mPar n V, fuel n] ∧ SameOutside μ μ' out 3

/-- core(n, V, x, b), with `V = 2U`: the input `X`, `n` numbers of absolute value at most `U`,
stands at `x`, below the free pointer `b`.  Returns 1 if three of the numbers, at different
positions, sum to 0, and 0 if not.  `T` and `r` are the time and the need of the Convolution-3SUM
solver. -/
def CoreSpec (lim : Limits) (P : Program) (p : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need) : Prop :=
  ∀ (d n U x b : ℕ) (X : List ℤ) (μ : ℕ → ℤ), X.length = n → AbsLe X U → Seg μ x X → x + n ≤ b →
    1 ≤ n → 1 ≤ U → (coreNeed r n (2 * U)).Ok lim b d →
    Meets lim P p d [n, ((2 * U : ℕ) : ℤ), x, b] μ (coreTime T n (2 * U)) fun res μ' =>
      res = flag (ThreeSum (vecOf n X)) ∧ Kept μ μ' b

end Light.Sec3.ChanHe
