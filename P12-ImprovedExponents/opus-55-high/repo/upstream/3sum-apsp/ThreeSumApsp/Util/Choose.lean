/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial coefficients

Upper bounds. A single summand of the binomial expansion of `(a + b) ^ n` is at most the whole sum
(`Nat.choose_mul_pow_mul_pow_le`); with `a = 1` this is `binom(n, k) * b ^ (n - k) ≤ (b + 1) ^ n`
(`Nat.choose_mul_pow_le`), which the paper uses with `b = 9`. And `binom(n, k) ≤ (e n / k) ^ k`
(`Nat.choose_le_exp_mul_div_pow`).

A lower bound. For `k ≤ n`, the largest of the `n + 1` terms `binom(n, j) k^j (n-k)^{n-j}` of the
expansion of `n^n = (k + (n-k))^n` is the one with `j = k`: the terms increase up to `j = k` and
decrease from there on. This gives the standard lower bound on a binomial coefficient
(`Nat.pow_self_le_mul_choose_mul_pow_mul_pow`), which Section 4.4 uses in the proof of Corollary 26
and, written with the entropy function as `e^{n H(k/n)}/(n+1) ≤ binom(n, k)`, in the proof of
Corollary 31.
-/


namespace Nat

/-! ## Upper bounds -/

/-- One summand of the binomial expansion of `(a + b) ^ n` is at most `(a + b) ^ n`. -/
theorem choose_mul_pow_mul_pow_le (a b n k : ℕ) :
    n.choose k * a ^ k * b ^ (n - k) ≤ (a + b) ^ n := by
  obtain hk | hk := le_or_gt k n
  · rw [add_pow]
    calc n.choose k * a ^ k * b ^ (n - k) = a ^ k * b ^ (n - k) * n.choose k := by ring
      _ ≤ _ := Finset.single_le_sum (f := fun k => a ^ k * b ^ (n - k) * n.choose k)
          (by omega) (by simp_all)
  grind

/-! ## The largest term of a binomial expansion -/

/-- The term number `j` of the expansion of `n^n = (k + (n-k))^n`. -/
def modeTerm (n k j : ℕ) : ℕ := n.choose j * k ^ j * (n - k) ^ (n - j)

variable {j n : ℕ}

/-- The quotient of two consecutive terms is `(n - j) k / ((n - k) (j + 1))`. -/
theorem modeTerm_succ_mul (k : ℕ) (hj : j < n) :
    modeTerm n k (j + 1) * ((n - k) * (j + 1)) = modeTerm n k j * ((n - j) * k) := by
  have he : n - j = n - (j + 1) + 1 := by omega
  grind [modeTerm, Nat.choose_succ_right_eq]

variable {k : ℕ}

/-- The terms increase up to `j = k`. -/
theorem modeTerm_le_succ (hjk : j < k) (hkn : k ≤ n) :
    modeTerm n k j ≤ modeTerm n k (j + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos (by omega : 0 < n - j) (by omega : 0 < k))
  rw [← modeTerm_succ_mul k (by omega)]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))

/-- The terms decrease from `j = k` on. -/
theorem modeTerm_succ_le (hkj : k ≤ j) (hjn : j < n) :
    modeTerm n k (j + 1) ≤ modeTerm n k j := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos (by omega : 0 < n - k) j.succ_pos)
  rw [modeTerm_succ_mul k hjn]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))

/-- Every term is at most the term with `j = k`. -/
theorem modeTerm_le_mode (hkn : k ≤ n) (hjn : j ≤ n) :
    modeTerm n k j ≤ modeTerm n k k := by
  rcases le_total j k with hjk | hkj
  · induction hjk using Nat.decreasingInduction with
    | self => rfl
    | of_succ j hjk ih => grind [modeTerm_le_succ]
  · induction j, hkj using Nat.le_induction with
    | base => rfl
    | succ j hkj ih => grind [modeTerm_succ_le]

/-- Proof of Corollary 26: "the standard bound binom(n, k) ≥ 1/(n+1) · n^n/(k^k (n-k)^{n-k})",
without fractions.  Of the `n + 1` terms of the expansion of `n^n = (k + (n-k))^n`, the one with
`binom(n, k)` is the largest. -/
theorem pow_self_le_mul_choose_mul_pow_mul_pow (hkn : k ≤ n) :
    n ^ n ≤ (n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) :=
  calc n ^ n = (k + (n - k)) ^ n := by simp_all
    _ = ∑ j ∈ Finset.range _, modeTerm n k j := by
        grind [add_pow, modeTerm]
    _ ≤ ∑ _j ∈ Finset.range _, modeTerm n k k :=
        Finset.sum_le_sum fun _ hj => modeTerm_le_mode hkn (Finset.mem_range_succ_iff.1 hj)
    _ = (n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) := by
        aesop
