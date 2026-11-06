/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Util.Flag

/-!
# The entries of a (min,+)-product, found bit by bit

Theorem 21(b), after [VW18, Theorem 4.2]: the (min,+)-product is computed
by a binary search for all entries at once.  An entry `c` with `-2U ≤ c ≤ 2U` is approached from
below: `bitLo U t c` is `c` with the lowest `t` bits of `c + 2U` cleared.

* The search starts at `t = R`, where `4U < 2^R`, with `-2U` (`bitLo_top`), and it ends at `t = 0`
  with `c` (`bitLo_zero`).
* One round goes from `t + 1` to `t`: it asks whether `c < bitLo U (t + 1) c + 2^t` and adds `2^t`
  if not (`bitLo_step`).
* The question is whether the pair `(i, j)` has a witness: `c` is below a number exactly if one of
  the sums `A[i,k] + B[k,j]` is (`exists_sum_lt_iff`).  So one round for all entries is one call of
  a routine that finds all pairs with a witness.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- Some sum `A[i,k] + B[k,j]` is below `z` exactly if the entry `(i, j)` of the product is. -/
theorem exists_sum_lt_iff {n} (hn : 1 ≤ n) A B i j z :
    (∃ k < n, entry n A i k + entry n B k j < z) ↔ minPlusEntry n A B i j < z := by
  constructor
  · rintro ⟨k, hk, h⟩
    exact (minPlusEntry_le n A B i j hk).trans_lt h
  · intro h
    obtain ⟨k, hk, he⟩ := exists_minPlusEntry_eq hn A B i j
    exact ⟨k, hk, he ▸ h⟩

/-- `c` with the lowest `t` bits of `c + 2U` cleared. -/
def bitLo U t c := -(2 * U) + (((c + 2 * U).toNat / 2 ^ t * 2 ^ t : ℕ) : ℤ)

/-- With no bit cleared the number is `c`: the end of the search. -/
theorem bitLo_zero {U c} (h : -(2 * U) ≤ c) : bitLo U 0 c = c := by
  simp_all [bitLo] <;> omega

/-- With all bits cleared the number is `-2U`: the start of the search. -/
theorem bitLo_top {U c} {R} (h : c + 2 * U < 2 ^ R) : bitLo U R c = -(2 * U) := by

  simp [bitLo, Nat.div_eq_of_lt (by
    simp_all
   : (c + 2 * U).toNat < 2 ^ R)]

/-- The search never goes below `-2U`. -/
theorem le_bitLo U t c : -(2 * U) ≤ bitLo U t c :=
  le_add_of_nonneg_right (Int.natCast_nonneg _)

/-- The search never goes above `c`. -/
theorem bitLo_le {U c} (h : -(2 * U) ≤ c) t : bitLo U t c ≤ c := by

  have  : ((c + 2 * U).toNat : ℤ) = c + 2 * U := Int.toNat_of_nonneg (by linarith)
  rw [bitLo]
  linarith [Int.ofNat_le.2 (Nat.div_mul_le_self _ _ : (c + 2 * U).toNat / 2 ^ t * 2 ^ t ≤ (c + 2 * U).toNat)]

/-- Clearing one bit less: the bit number `t` of `y` is 0 exactly if `y` is less than `2^t` above
`y` with its lowest `t + 1` bits cleared. -/
private theorem div_mul_pow_step y t :
    y / 2 ^ t * 2 ^ t = y / 2 ^ (t + 1) * 2 ^ (t + 1) +
      if y < y / 2 ^ (t + 1) * 2 ^ (t + 1) + 2 ^ t then 0 else 2 ^ t := by
  have hp : 0 < 2 ^ t := by positivity
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  generalize 2 ^ t = p at hp
  have hlow := Nat.div_mul_le_self y p
  have hhigh : y < y / p * p + p := Nat.lt_div_mul_add hp
  generalize y / p = q at hlow hhigh
  rcases Nat.even_or_odd' q with ⟨b, rfl | rfl⟩
  · grind
  · grind

/-- **One round of the search**: `bitLo U t c` is `bitLo U (t + 1) c`, plus `2^t` unless
`c < bitLo U (t + 1) c + 2^t`. -/
theorem bitLo_step {U c} (h : -(2 * U) ≤ c) t :
    bitLo U t c = bitLo U (t + 1) c + 2 ^ t * (1 - flag (c < bitLo U (t + 1) c + 2 ^ t)) := by



  simp only [bitLo, div_mul_pow_step (c + 2 * U).toNat t]
  grind [flag_of, flag_of_not]

end ThreeSumApsp.Spec
