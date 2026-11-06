/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.NumberTheory.Chebyshev

/-!
# Counting the primes up to m, in natural numbers

Three elementary bounds on the number `π(m)` of primes up to `m`, the cardinality of
`Nat.primesLE m`.

* `π(m) ≤ m` (`Nat.card_primesLE_le`).
* `m ≤ (⌊log₂ m⌋ + 1)(π(m) + 1)` (`Nat.le_log_mul_card_primesLE`), from the bound
  `2^m ≤ (m + 1) lcm(1, …, m)` of Mathlib: each prime power in the least common multiple is at most
  `m`.
* So there are at least `w` primes up to `(w + 1)(2⌊log₂(w + 1)⌋ + 4)`
  (`Nat.le_card_primesLE_mul_log`).
-/


namespace Nat

open Finset

variable (m : ℕ)

/-- There are at most `m` primes up to `m`. -/
theorem card_primesLE_le : #(Nat.primesLE m) ≤ m := by
  rw [Nat.primesLE_eq_filter_Icc_one]
  exact (card_filter_le _ _).trans_eq (by simp)

/-- A lower bound of Chebyshev's type in natural numbers: `m ≤ (⌊log₂ m⌋ + 1)(π(m) + 1)`. -/
theorem le_log_mul_card_primesLE : m ≤ (Nat.log 2 m + 1) * (#(Nat.primesLE m) + 1) := by
  rcases m.eq_zero_or_pos with rfl | hm
  · simp
  set l := Nat.log 2 m
  have hlt : m < 2 ^ (l + 1) := by grind [Nat.lt_pow_succ_log_self]
  apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
  calc 2 ^ m ≤ (m + 1) * m.lcmUpto := Chebyshev.two_pow_le_mul_lcmUpto m
    _ = (m + 1) * ∏ p ∈ m.primesLE, p ^ p.log m := by rw [Nat.lcmUpto_eq_prod_pow_log]
    _ ≤ 2 ^ (l + 1) * (2 ^ (l + 1)) ^ #(Nat.primesLE m) := Nat.mul_le_mul hlt
        (prod_le_pow_card _ _ _ fun p _ => by grind [Nat.pow_log_le_self])
    _ = 2 ^ ((l + 1) * (#(Nat.primesLE m) + 1)) := by grind [pow_succ', pow_mul]

/-- There are at least `w` primes up to `(w + 1)(2⌊log₂(w + 1)⌋ + 4)`. -/
theorem le_card_primesLE_mul_log (w : ℕ) :
    w ≤ #(Nat.primesLE ((w + 1) * (2 * Nat.log 2 (w + 1) + 4))) := by
  set a := Nat.log 2 _
  set m := (w + 1) * (2 * a + 4) with hm
  have hw : w + 1 < 2 ^ (a + 1) := by grind [Nat.lt_pow_succ_log_self]
  have ha : 2 * a + 4 ≤ 2 ^ (a + 2) := by
    grind [Nat.lt_two_pow_self]
  have hlt :=
    calc (2 * a + 3) * (w + 1) < (2 * a + 4) * (w + 1) :=
          by simp
      _ = m := by grind
      _ ≤ (Nat.log 2 m + 1) * (#(Nat.primesLE m) + 1) := le_log_mul_card_primesLE m
      _ ≤ (2 * a + 3) * (#(Nat.primesLE m) + 1) := Nat.mul_le_mul_right _ (Nat.log_lt_of_lt_pow (by positivity) <|
    calc m < 2 ^ (a + 1) * 2 ^ (a + 2) := by simp_all [Nat.mul_lt_mul_of_lt_of_le]
      _ = 2 ^ (2 * a + 3) := by rw [← pow_add]; grind)
  have := Nat.lt_of_mul_lt_mul_left hlt
  omega
