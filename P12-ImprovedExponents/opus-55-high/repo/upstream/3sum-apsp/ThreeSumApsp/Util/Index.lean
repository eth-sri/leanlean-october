/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.Ring.Int

/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/


namespace Nat

variable {m a n b : ℕ}

/-! ## Bounds on an index -/

/-- The index of an entry of a matrix with `m` rows and `n` columns is below `m * n`. -/
theorem mul_add_lt_mul (ha : a < m) (hb : b < n) : a * n + b < m * n :=
  a.mul_comm n ▸ Nat.mul_add_lt_mul_of_lt_of_lt ha hb

/-- Row `a < m` ends within the matrix: `a * n + b ≤ m * n` for `b ≤ n`, so also for `b = n`. -/
theorem mul_add_le_mul (ha : a < m) (hb : b ≤ n) : a * n + b ≤ m * n :=
  calc a * n + b ≤ a * n + n := by omega
    _ = (a + 1) * n := by grind
    _ ≤ m * n := Nat.mul_le_mul_right n ha

/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/

/-- The row of the index `a * n + b`. -/
theorem mul_add_div_of_lt (hb : b < n) : (a * n + b) / n = a := by
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hb), Nat.div_eq_of_lt hb, Nat.add_zero]

/-- The index determines the pair. -/
theorem mul_add_inj_of_lt {a' b' : ℕ} (hb : b < n) (hb' : b' < n)
    (h : a * n + b = a' * n + b') :
    a = a' ∧ b = b' :=
  by grind [mul_add_div_of_lt, Nat.mul_add_mod_of_lt]

variable {t : ℕ}

/-- The row of an index below `m * n` is below `m`. -/
theorem div_lt_of_lt_mul' (h : t < m * n) : t / n < m :=
  Nat.div_lt_of_lt_mul (by grind)

/-- The column of an index below `m * n` is below `n`. -/
theorem mod_lt_of_lt_mul (h : t < m * n) : t % n < n :=
  t.mod_lt (by grind)

/-- Every index below `m * n` is the index of a pair. -/
theorem exists_eq_mul_add_of_lt_mul (h : t < m * n := by aesop) : ∃ a < m, ∃ b < n, t = a * n + b :=
  ⟨t / n, div_lt_of_lt_mul' h, t % n, mod_lt_of_lt_mul h, by grind [Nat.div_add_mod']⟩

variable {i : ℕ}

/-- The indices of the diagonal are the multiples of `n + 1`. -/
theorem eq_mul_succ_iff (hi : i < n) : t = i * (n + 1) ↔ t / n = i ∧ t % n = i := by
  grind [mul_add_div_of_lt, Nat.mul_add_mod_of_lt, Nat.mul_succ, Nat.div_add_mod']

/-! ## The next index -/

/-- The next index, if it is in the same row. -/
theorem succ_div_mod_of_lt (h : i % n + 1 < n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 := by
  have hsucc : i + 1 = i / n * n + (i % n + 1) := by grind [Nat.add_assoc, Nat.div_add_mod']
  exact ⟨by simp_all [mul_add_div_of_lt], by rw [hsucc, Nat.mul_add_mod_of_lt h]⟩

/-- The next index, if the test "is this the end of the row?" fails. -/
theorem succ_div_mod_of_ne (hn : 0 < n) (h : i % n + 1 ≠ n) :
    (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1 :=
  succ_div_mod_of_lt (lt_of_le_of_ne (Nat.mod_lt i hn) h)

/-- After the last index of a row comes the first index of the next row. -/
theorem succ_div_mod_of_eq (h : i % n + 1 = n) :
    (i + 1) / n = i / n + 1 ∧ (i + 1) % n = 0 := by
  have hn : 0 < n := by omega
  have hsucc : i + 1 = (i / n + 1) * n + 0 := by
    grind [Nat.div_add_mod']
  simp_all

end Nat

namespace Int

variable {M : ℕ}

/-! ## Residues as natural numbers -/

/-- The residue of an integer modulo `M ≥ 1`, as a natural number, is below `M`. -/
theorem toNat_emod_lt (hM : 0 < M) (x : ℤ) : (x % (M : ℤ)).toNat < M := by
  simp_all [Int.emod_lt_of_pos, Int.natCast_pos]

/-- The residue of an integer modulo `M ≥ 1` is a natural number. -/
theorem natCast_toNat_emod (hM : 0 < M) (x : ℤ) : ((x % (M : ℤ)).toNat : ℤ) = x % (M : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg x (Int.natCast_ne_zero_iff_pos.2 hM))
