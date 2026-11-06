module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.NumberTheory.Chebyshev
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Definitions
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Few indices are far above the average

Let `f` be a function with natural numbers as values on a nonempty finite set `Q`.  Division is
avoided: "`f p` is at most `k` times the average of `f`" is written
`f p * |Q| ≤ k * ∑ p' ∈ Q, f p'`.

* Fewer than `|Q|/k` indices are more than `k` times as bad as the average
  (`Finset.mul_card_above_average_lt`, Markov's inequality).
* So for `k` functions there is one index at which each of them is at most `k` times its average
  (`Finset.exists_forall_mul_card_le_mul_sum`, the union bound).
-/


namespace Finset

/-- Markov's inequality: fewer than `|Q|/k` indices are more than `k` times as bad as the
average. -/
theorem mul_card_above_average_lt {ι : Type*} {Q : Finset ι} (hQ : Q.Nonempty) (k : ℕ)
    (f : ι → ℕ) : k * #{p ∈ Q | k * ∑ p' ∈ Q, f p' < f p * #Q} < #Q := by
  set B := {p ∈ Q | k * ∑ p' ∈ Q, f p' < f p * #Q}
  rcases B.eq_empty_or_nonempty with he | hne
  · rw [he, card_empty, mul_zero]
    exact hQ.card_pos
  refine lt_of_mul_lt_mul_right (a := ∑ p ∈ Q, f p) ?_ (Nat.zero_le _)
  calc k * #B * ∑ p ∈ Q, f p = ∑ _p ∈ B, k * ∑ p' ∈ Q, f p' := by
        rw [sum_const, smul_eq_mul]; ring
    _ < ∑ p ∈ B, f p * #Q := sum_lt_sum_of_nonempty hne fun p hp => (mem_filter.mp hp).2
    _ ≤ ∑ p ∈ Q, f p * #Q := sum_le_sum_of_subset (filter_subset _ _)
    _ = #Q * ∑ p ∈ Q, f p := by rw [← sum_mul, mul_comm]

/-- The union bound: one index is good for `k` functions at once, in that each function is at most
`k` times its average there. -/
theorem exists_forall_mul_card_le_mul_sum {ι : Type*} {Q : Finset ι} (hQ : Q.Nonempty) (k : ℕ)
    (f : Fin k → ι → ℕ) : ∃ p ∈ Q, ∀ i, f i p * #Q ≤ k * ∑ p' ∈ Q, f i p' := by
  classical
  by_contra hcon
  push Not at hcon
  set B : Fin k → Finset ι := fun i => {p ∈ Q | k * ∑ p' ∈ Q, f i p' < f i p * #Q}
  have hcover : Q ⊆ univ.biUnion B := fun p hp =>
    let ⟨i, hi⟩ := hcon p hp
    mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨hp, hi⟩⟩
  -- there is at least one function, which the strict inequality below needs
  obtain ⟨i₀, -⟩ := hcon _ hQ.choose_spec
  refine lt_irrefl (k * #Q) ?_
  calc k * #Q ≤ k * ∑ i, #(B i) :=
        Nat.mul_le_mul_left _ ((card_le_card hcover).trans card_biUnion_le)
    _ = ∑ i, k * #(B i) := mul_sum ..
    _ < ∑ _i : Fin k, #Q :=
        sum_lt_sum_of_nonempty ⟨i₀, mem_univ i₀⟩ fun i _ => mul_card_above_average_lt hQ k (f i)
    _ = k * #Q := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end Finset

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


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

/-- There are at most `m` primes up to `m`. -/
theorem card_primesLE_le (m : ℕ) : #(Nat.primesLE m) ≤ m := by
  rw [Nat.primesLE_eq_filter_Icc_one]
  exact (card_filter_le _ _).trans_eq (by simp)

/-- A lower bound of Chebyshev's type in natural numbers: `m ≤ (⌊log₂ m⌋ + 1)(π(m) + 1)`. -/
theorem le_log_mul_card_primesLE (m : ℕ) : m ≤ (Nat.log 2 m + 1) * (#(Nat.primesLE m) + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set l := Nat.log 2 m
  have hlt : m < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ?_
  calc 2 ^ m ≤ (m + 1) * Nat.lcmUpto m := Chebyshev.two_pow_le_mul_lcmUpto m
    _ = (m + 1) * ∏ p ∈ Nat.primesLE m, p ^ p.log m := by rw [Nat.lcmUpto_eq_prod_pow_log]
    _ ≤ 2 ^ (l + 1) * (2 ^ (l + 1)) ^ #(Nat.primesLE m) := Nat.mul_le_mul hlt
        (prod_le_pow_card _ _ _ fun p _ => (Nat.pow_log_le_self p hm.ne').trans hlt.le)
    _ = 2 ^ ((l + 1) * (#(Nat.primesLE m) + 1)) := by rw [← pow_succ', ← pow_mul]

/-- There are at least `w` primes up to `(w + 1)(2⌊log₂(w + 1)⌋ + 4)`. -/
theorem le_card_primesLE_mul_log (w : ℕ) :
    w ≤ #(Nat.primesLE ((w + 1) * (2 * Nat.log 2 (w + 1) + 4))) := by
  set a := Nat.log 2 (w + 1)
  set m := (w + 1) * (2 * a + 4) with hm
  have hw : w + 1 < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have ha : 2 * a + 4 ≤ 2 ^ (a + 2) := by
    have := Nat.lt_two_pow_self (n := a + 1)
    rw [pow_succ]
    omega
  have hlog : Nat.log 2 m < 2 * a + 3 := Nat.log_lt_of_lt_pow (by positivity) <|
    calc m < 2 ^ (a + 1) * 2 ^ (a + 2) := Nat.mul_lt_mul_of_lt_of_le hw ha (by positivity)
      _ = 2 ^ (2 * a + 3) := by rw [← pow_add]; congr 1; omega
  have hlt : (2 * a + 3) * (w + 1) < (2 * a + 3) * (#(Nat.primesLE m) + 1) :=
    calc (2 * a + 3) * (w + 1) < (2 * a + 4) * (w + 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = m := mul_comm _ _
      _ ≤ (Nat.log 2 m + 1) * (#(Nat.primesLE m) + 1) := le_log_mul_card_primesLE m
      _ ≤ (2 * a + 3) * (#(Nat.primesLE m) + 1) := Nat.mul_le_mul_right _ hlog
  have := Nat.lt_of_mul_lt_mul_left hlt
  omega

end Nat

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Theorem 21(a), the reduction of Chan and He: the choice of the modulus

For Theorem 21(a): the deterministic reduction from 3SUM to
Convolution-3SUM after [CH20, Theorem 5.1] hashes the numbers by `x ↦ x mod pq`, for two primes
`p` and `q` that it finds by exhaustive search among the primes up to `m = mPar n U`.  This file
shows that both searches succeed and that few elements are badly hashed.

* An ordered pair of distinct elements of a set `S` collides modulo `M` if `M` divides their
  difference; `coll S M` counts these ordered pairs.  An element that collides with another one is
  heavy.  There are at most as many heavy elements as colliding pairs (`card_heavy_le_coll`).  The
  count is determined by the sizes of the residue classes (`coll_eq_sum`); the proofs below do not
  need this, a program that computes the count does.
* A nonzero difference has at most `Λ = Lam U` prime divisors.  So, summed over the candidates `q`
  in the set `Q` of primes that a search goes through, the pairs that collide modulo `M₀ q` number
  at most `Λ` times those that collide modulo `M₀` (`sum_coll_mul_le`).
* By counting (the finite form of Markov's inequality and of the union bound, which [CH20] uses),
  some candidate is, for each of the three sets, at most three times as bad as the average
  (`Finset.exists_forall_mul_card_le_mul_sum`, `exists_prime_coll_le`). So both searches succeed
  (`firstP_spec`, `secondP_spec`), and the modulus `pq` leaves at most `9Λ²|S|²/|Q|²` colliding
  pairs in each set `S` (`modulus_spec`).
* There are at least `wPar n U` primes up to `mPar n U` (`wPar_le_card_primesLE`, from the bound
  `2^m ≤ (m + 1) lcm(1, …, m)` of Mathlib).  With that many candidates a set `S` has at most
  `|S|²/(2n)` heavy elements (`card_heavy_modulus_le`, `le_card_primesLE_mPar_sq`).
-/


namespace ThreeSumApsp

namespace ChanHe

open Finset

/-! ## Colliding pairs and heavy elements -/

/-- Two integers are congruent modulo `M` iff they have the same remainder. -/
theorem natCast_dvd_sub_iff_emod_eq (M : ℕ) (x y : ℤ) :
    (M : ℤ) ∣ x - y ↔ x % (M : ℤ) = y % (M : ℤ) :=
  Int.modEq_iff_dvd.symm.trans eq_comm

/-- Each heavy element is the first component of a colliding pair. -/
theorem card_heavy_le_coll (S : Finset ℤ) (M : ℕ) : #(heavy S M) ≤ coll S M := by
  refine (card_le_card fun x hx => ?_).trans (card_image_le (f := Prod.fst))
  obtain ⟨hxS, y, hyS, hne, hd⟩ := mem_filter.mp hx
  exact mem_image.mpr ⟨(x, y), mem_filter.mpr ⟨mem_offDiag.mpr ⟨hxS, hyS, hne.symm⟩, hd⟩, rfl⟩

/-- There are at most `|S|²` colliding ordered pairs. -/
theorem coll_le_sq (S : Finset ℤ) (M : ℕ) : coll S M ≤ #S ^ 2 :=
  calc coll S M ≤ #S.offDiag := card_filter_le _ _
    _ = #S * #S - #S := offDiag_card S
    _ ≤ #S ^ 2 := by rw [sq]; omega

/-- The collision count is determined by the sizes of the buckets: an element collides with the
other members of its bucket. -/
theorem coll_eq_sum (S : Finset ℤ) (M : ℕ) :
    coll S M = ∑ x ∈ S, (#(bucket S M (x % (M : ℤ))) - 1) := by
  have hfiber : ∀ x ∈ S,
      #(bucket S M (x % (M : ℤ))) - 1 = #{y ∈ S | x ≠ y ∧ (M : ℤ) ∣ x - y} := by
    intro x hx
    rw [← card_erase_of_mem (show x ∈ bucket S M (x % (M : ℤ)) from mem_filter.mpr ⟨hx, rfl⟩)]
    congr 1
    ext y
    simp only [bucket, mem_filter, mem_erase, natCast_dvd_sub_iff_emod_eq, ne_comm (a := x),
      eq_comm (a := x % _)]
    tauto
  have hpairs : {p ∈ S.offDiag | (M : ℤ) ∣ p.1 - p.2} =
      {p ∈ S ×ˢ S | p.1 ≠ p.2 ∧ (M : ℤ) ∣ p.1 - p.2} := by
    ext p
    simp only [mem_filter, mem_offDiag, mem_product, and_assoc]
  rw [sum_congr rfl hfiber, coll, hpairs, card_filter, sum_product]
  simp only [card_filter]

/-- `Lam U` is at least 1. -/
theorem Lam_pos (U : ℕ) : 1 ≤ Lam U := Nat.succ_pos _

/-- A nonzero integer of absolute value at most `2U` is divisible by at most `Lam U` primes,
because their product divides it. -/
theorem card_prime_divisors_le {Q : Finset ℕ} (hP : ∀ p ∈ Q, p.Prime) {U : ℕ} {d : ℤ}
    (hd : d ≠ 0) (hb : |d| ≤ 2 * (U : ℤ)) : #{p ∈ Q | ((p : ℕ) : ℤ) ∣ d} ≤ Lam U := by
  set T := {p ∈ Q | ((p : ℕ) : ℤ) ∣ d}
  have hprime : ∀ p ∈ T, p.Prime := fun p hp => hP p (mem_filter.mp hp).1
  have hsub : T ⊆ d.natAbs.primeFactors := fun p hp => Nat.mem_primeFactors.mpr
    ⟨hprime p hp, Int.natCast_dvd.mp (mem_filter.mp hp).2, Int.natAbs_ne_zero.mpr hd⟩
  have hpow : 2 ^ #T ≤ 2 * U :=
    calc 2 ^ #T ≤ ∏ p ∈ T, p := pow_card_le_prod _ _ _ fun p hp => (hprime p hp).two_le
      _ ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hd)
          ((prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd _))
      _ ≤ 2 * U := by have := abs_le.mp hb; omega
  exact (Nat.le_log_of_pow_le (by norm_num) hpow).trans (Nat.le_succ _)

/-- Double counting.  Summed over the candidates `q ∈ Q`, the pairs that collide modulo `M₀ q`
number at most `Lam U` times those that collide modulo `M₀`: such a pair collides modulo `M₀`, and
`q` divides its difference.  Coprimality of `q` and `M₀` is not used, so the two primes of a modulus
are allowed to coincide. -/
theorem sum_coll_mul_le {Q : Finset ℕ} (hP : ∀ p ∈ Q, p.Prime) {U : ℕ} {S : Finset ℤ}
    (hS : Bdd U S) (M₀ : ℕ) : ∑ q ∈ Q, coll S (M₀ * q) ≤ Lam U * coll S M₀ := by
  set C := {xy ∈ S.offDiag | (M₀ : ℤ) ∣ xy.1 - xy.2}
  calc ∑ q ∈ Q, coll S (M₀ * q)
      ≤ ∑ q ∈ Q, #{xy ∈ C | (q : ℤ) ∣ xy.1 - xy.2} := by
        refine sum_le_sum fun q _ => card_le_card fun xy h => ?_
        obtain ⟨hxy, hd⟩ := mem_filter.mp h
        rw [Nat.cast_mul] at hd
        exact mem_filter.mpr
          ⟨mem_filter.mpr ⟨hxy, dvd_of_mul_right_dvd hd⟩, dvd_of_mul_left_dvd hd⟩
    _ = ∑ xy ∈ C, #{q ∈ Q | ((q : ℕ) : ℤ) ∣ xy.1 - xy.2} :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ ≤ ∑ _xy ∈ C, Lam U := by
        refine sum_le_sum fun xy h => ?_
        obtain ⟨hx, hy, hne⟩ := mem_offDiag.mp (mem_filter.mp h).1
        exact card_prime_divisors_le hP (sub_ne_zero.mpr hne)
          ((abs_sub _ _).trans (by linarith [hS _ hx, hS _ hy]))
    _ = Lam U * coll S M₀ := by rw [sum_const, smul_eq_mul, mul_comm, coll]

/-! ## The two searches succeed -/

section searches

variable {Q : Finset ℕ} {U : ℕ} {S₁ S₂ S₃ : Finset ℤ}

/-- On a nonempty set, `pick` returns a member. -/
theorem pick_mem {T : Finset ℕ} (h : T.Nonempty) : pick T ∈ T := by
  rw [pick, dif_pos h]
  exact T.min'_mem h

/-- Some candidate `q` is good for the three sets at once: in each of them at most the fraction
`3Λ/|Q|` of the pairs that collide modulo `M₀` still collide modulo `M₀ q`. -/
theorem exists_prime_coll_le (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁)
    (h₂ : Bdd U S₂) (h₃ : Bdd U S₃) (M₀ : ℕ) :
    ∃ q ∈ Q, coll S₁ (M₀ * q) * #Q ≤ 3 * Lam U * coll S₁ M₀ ∧
      coll S₂ (M₀ * q) * #Q ≤ 3 * Lam U * coll S₂ M₀ ∧
      coll S₃ (M₀ * q) * #Q ≤ 3 * Lam U * coll S₃ M₀ := by
  obtain ⟨q, hq, hgood⟩ :=
    Finset.exists_forall_mul_card_le_mul_sum hQ 3 fun i q => coll (![S₁, S₂, S₃] i) (M₀ * q)
  have havg : ∀ {S : Finset ℤ}, Bdd U S →
      3 * ∑ q' ∈ Q, coll S (M₀ * q') ≤ 3 * Lam U * coll S M₀ := fun hS => by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (sum_coll_mul_le hP hS M₀)
  exact ⟨q, hq, (hgood 0).trans (havg h₁), (hgood 1).trans (havg h₂), (hgood 2).trans (havg h₃)⟩

/-- The first search succeeds: `firstP` lies in `Q` and passes its three tests. -/
theorem firstP_spec (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) :
    firstP Q (Lam U) S₁ S₂ S₃ ∈ {p ∈ Q | coll S₁ p * #Q ≤ 3 * Lam U * #S₁ ^ 2 ∧
      coll S₂ p * #Q ≤ 3 * Lam U * #S₂ ^ 2 ∧ coll S₃ p * #Q ≤ 3 * Lam U * #S₃ ^ 2} := by
  obtain ⟨p, hp, c₁, c₂, c₃⟩ := exists_prime_coll_le hQ hP h₁ h₂ h₃ 1
  rw [one_mul] at c₁ c₂ c₃
  have hall : ∀ S : Finset ℤ, 3 * Lam U * coll S 1 ≤ 3 * Lam U * #S ^ 2 :=
    fun S => Nat.mul_le_mul_left _ (coll_le_sq S 1)
  exact pick_mem
    ⟨p, mem_filter.mpr ⟨hp, c₁.trans (hall S₁), c₂.trans (hall S₂), c₃.trans (hall S₃)⟩⟩

/-- The second search succeeds, for any first factor `p`. -/
theorem secondP_spec (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) (p : ℕ) :
    secondP Q (Lam U) S₁ S₂ S₃ p ∈ {q ∈ Q | coll S₁ (p * q) * #Q ≤ 3 * Lam U * coll S₁ p ∧
      coll S₂ (p * q) * #Q ≤ 3 * Lam U * coll S₂ p ∧
      coll S₃ (p * q) * #Q ≤ 3 * Lam U * coll S₃ p} := by
  obtain ⟨q, hq, hc⟩ := exists_prime_coll_le hQ hP h₁ h₂ h₃ p
  exact pick_mem ⟨q, mem_filter.mpr ⟨hq, hc⟩⟩

/-- Both searches succeed, and the modulus leaves at most `9Λ²|S|²/|Q|²` colliding pairs in each of
the three sets.  (A search that fails returns 1, which is not in `Q`.) -/
theorem modulus_spec (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) :
    firstP Q (Lam U) S₁ S₂ S₃ ∈ Q ∧ secondP Q (Lam U) S₁ S₂ S₃ (firstP Q (Lam U) S₁ S₂ S₃) ∈ Q ∧
    ∀ S ∈ [S₁, S₂, S₃], coll S (modulus Q (Lam U) S₁ S₂ S₃) * #Q ^ 2 ≤ 9 * Lam U ^ 2 * #S ^ 2 := by
  obtain ⟨hp, p₁, p₂, p₃⟩ := mem_filter.mp (firstP_spec hQ hP h₁ h₂ h₃)
  obtain ⟨hq, q₁, q₂, q₃⟩ :=
    mem_filter.mp (secondP_spec hQ hP h₁ h₂ h₃ (firstP Q (Lam U) S₁ S₂ S₃))
  -- the two tests multiply: `c` counts collisions modulo `pq`, `c'` modulo `p`, and `s = |S|`
  have hmul : ∀ {c c' s : ℕ}, c' * #Q ≤ 3 * Lam U * s ^ 2 → c * #Q ≤ 3 * Lam U * c' →
      c * #Q ^ 2 ≤ 9 * Lam U ^ 2 * s ^ 2 := fun {c c' s} hfirst hsecond =>
    calc c * #Q ^ 2 = c * #Q * #Q := by ring
      _ ≤ 3 * Lam U * c' * #Q := Nat.mul_le_mul_right _ hsecond
      _ = 3 * Lam U * (c' * #Q) := by ring
      _ ≤ 3 * Lam U * (3 * Lam U * s ^ 2) := Nat.mul_le_mul_left _ hfirst
      _ = 9 * Lam U ^ 2 * s ^ 2 := by ring
  refine ⟨hp, hq, fun S hS => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl
  · exact hmul p₁ q₁
  · exact hmul p₂ q₂
  · exact hmul p₃ q₃

/-- The modulus lies between 1 and `m²` when all primes in `Q` are at most `m`. -/
theorem modulus_bounds (hQ : Q.Nonempty) (hP : ∀ p ∈ Q, p.Prime) {m : ℕ} (hm : ∀ p ∈ Q, p ≤ m)
    (h₁ : Bdd U S₁) (h₂ : Bdd U S₂) (h₃ : Bdd U S₃) :
    1 ≤ modulus Q (Lam U) S₁ S₂ S₃ ∧ modulus Q (Lam U) S₁ S₂ S₃ ≤ m ^ 2 := by
  obtain ⟨hp, hq, -⟩ := modulus_spec hQ hP h₁ h₂ h₃
  exact ⟨Nat.mul_pos (hP _ hp).pos (hP _ hq).pos, sq m ▸ Nat.mul_le_mul (hm _ hp) (hm _ hq)⟩

/-- The hypothesis of `card_heavy_modulus_le` on the number of candidates implies that there is
one. -/
theorem nonempty_of_le_card_sq {n : ℕ} (hbig : 18 * Lam U ^ 2 * n ≤ #Q ^ 2) (hn : 1 ≤ n) :
    Q.Nonempty := by
  have hpos : 0 < 18 * Lam U ^ 2 * n := by have := Lam_pos U; positivity
  exact card_pos.mp ((pow_pos_iff two_ne_zero).mp (hpos.trans_le hbig))

/-- With at least `√(18n) Λ` primes to choose from, each of the three sets `S` has at most
`|S|²/(2n)` heavy elements.  This is why the sizes of the sets fall doubly exponentially along the
recursion. -/
theorem card_heavy_modulus_le (hP : ∀ p ∈ Q, p.Prime) {n : ℕ}
    (hbig : 18 * Lam U ^ 2 * n ≤ #Q ^ 2) (hn : 1 ≤ n) (h₁ : Bdd U S₁) (h₂ : Bdd U S₂)
    (h₃ : Bdd U S₃) :
    ∀ S ∈ [S₁, S₂, S₃], 2 * n * #(heavy S (modulus Q (Lam U) S₁ S₂ S₃)) ≤ #S ^ 2 := by
  intro S hS
  obtain ⟨-, -, hcoll⟩ := modulus_spec (nonempty_of_le_card_sq hbig hn) hP h₁ h₂ h₃
  set M := modulus Q (Lam U) S₁ S₂ S₃
  have hΛ : 0 < 9 * Lam U ^ 2 := by have := Lam_pos U; positivity
  refine Nat.le_of_mul_le_mul_left ?_ hΛ
  calc 9 * Lam U ^ 2 * (2 * n * #(heavy S M))
      ≤ 9 * Lam U ^ 2 * (2 * n * coll S M) := by gcongr; exact card_heavy_le_coll S M
    _ = coll S M * (18 * Lam U ^ 2 * n) := by ring
    _ ≤ coll S M * #Q ^ 2 := Nat.mul_le_mul_left _ hbig
    _ ≤ 9 * Lam U ^ 2 * #S ^ 2 := hcoll S hS

end searches

/-! ## Enough primes -/

/-- There are at least `wPar n U` primes up to `mPar n U`. -/
theorem wPar_le_card_primesLE (n U : ℕ) : wPar n U ≤ #(Nat.primesLE (mPar n U)) :=
  Nat.le_card_primesLE_mul_log _

/-- The primes up to `mPar n U` are enough for `card_heavy_modulus_le`. -/
theorem le_card_primesLE_mPar_sq (n U : ℕ) : 18 * Lam U ^ 2 * n ≤ #(Nat.primesLE (mPar n U)) ^ 2 :=
  calc 18 * Lam U ^ 2 * n ≤ 25 * Lam U ^ 2 * ((Nat.sqrt n + 1) * (Nat.sqrt n + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by norm_num)) (Nat.lt_succ_sqrt n).le
    _ = wPar n U ^ 2 := by unfold wPar; ring
    _ ≤ #(Nat.primesLE (mPar n U)) ^ 2 := Nat.pow_le_pow_left (wPar_le_card_primesLE n U) 2

end ChanHe



namespace ChanHe

open Finset

/-! ## Light elements and the cells of the arrays -/

section cells

variable {S : Finset ℤ} {M U : ℕ}

/-- The elements of `S` that are alone in their residue class modulo `M`.  They play the role of
the good elements of [CH20]. -/
def light (S : Finset ℤ) (M : ℕ) : Finset ℤ := S \ heavy S M

/-- An element is light iff it collides with no other element. -/
theorem mem_light {x : ℤ} : x ∈ light S M ↔ x ∈ S ∧ ∀ y ∈ S, y ≠ x → ¬ (M : ℤ) ∣ x - y := by
  simp only [light, heavy, mem_sdiff, mem_filter, not_and, not_exists]
  exact and_congr_right fun h => ⟨fun g => g h, fun g _ => g⟩

/-- Light elements are elements. -/
theorem light_subset (S : Finset ℤ) (M : ℕ) : light S M ⊆ S := sdiff_subset

/-- Heavy elements are elements. -/
theorem heavy_subset (S : Finset ℤ) (M : ℕ) : heavy S M ⊆ S := filter_subset _ _

/-- A subset of a bounded set is bounded. -/
theorem Bdd.mono {S T : Finset ℤ} (h : Bdd U S) (hT : T ⊆ S) : Bdd U T := fun x hx => h x (hT hx)

/-- The bucket of a light element contains nothing else. -/
theorem bucket_of_light {x : ℤ} (hx : x ∈ light S M) : bucket S M (x % (M : ℤ)) = {x} := by
  obtain ⟨hxS, halone⟩ := mem_light.mp hx
  refine eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨hxS, rfl⟩, fun y hy => ?_⟩
  obtain ⟨hyS, hmod⟩ := mem_filter.mp hy
  by_contra hne
  exact halone y hyS hne ((natCast_dvd_sub_iff_emod_eq M x y).mpr hmod.symm)

/-- A light element sits in the cell of its remainder. -/
theorem arr_of_light {x : ℤ} (hx : x ∈ light S M) (pd : ℤ) {i : ℕ}
    (hi : (i : ℤ) = x % (M : ℤ)) : arr S M pd i = x := by
  rw [arr, hi, bucket_of_light hx, card_singleton, if_pos rfl, sum_singleton]

/-- A cell of the array holds a light element or padding. -/
theorem arr_mem_light_or_eq (S : Finset ℤ) (M : ℕ) (pd : ℤ) (i : ℕ) :
    arr S M pd i ∈ light S M ∨ arr S M pd i = pd := by
  unfold arr
  split_ifs with h
  · left
    obtain ⟨x, hx⟩ := card_eq_one.mp h
    have hmem : ∀ y, y ∈ bucket S M i ↔ y = x := fun y => by rw [hx, mem_singleton]
    obtain ⟨hxS, hxi⟩ := mem_filter.mp ((hmem x).mpr rfl)
    rw [hx, sum_singleton]
    refine mem_light.mpr ⟨hxS, fun y hy hne hd => hne ((hmem y).mp (mem_filter.mpr ⟨hy, ?_⟩))⟩
    rw [← hxi]
    exact ((natCast_dvd_sub_iff_emod_eq M x y).mp hd).symm
  · exact .inr rfl

/-- Negation preserves lightness. -/
theorem neg_mem_light_neg (S : Finset ℤ) (M : ℕ) (c : ℤ) :
    -c ∈ light (S.image fun c => -c) M ↔ c ∈ light S M := by
  simp only [mem_light, mem_image, neg_inj, exists_eq_right, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, ne_eq, ← neg_sub', dvd_neg]

/-- A cell of the first or second array holds a light element or `pad U`. -/
theorem arrXY_cases (M : ℕ) (h : Bdd U S) (i : ℕ) :
    (arrXY S M U i ∈ light S M ∧ |arrXY S M U i| ≤ U) ∨ arrXY S M U i = pad U :=
  (arr_mem_light_or_eq S M (pad U) i).imp_left fun hx => ⟨hx, h _ (light_subset S M hx)⟩

/-- A cell of the third array holds `-c` for a light element `c`, or `-pad U`. -/
theorem arrZ_cases (M : ℕ) (h : Bdd U S) (k : ℕ) :
    (∃ c ∈ light S M, |c| ≤ U ∧ arrZ S M U k = -c) ∨ arrZ S M U k = -pad U := by
  unfold arrZ
  split_ifs with hk
  · refine (arr_mem_light_or_eq (S.image fun c => -c) M (-pad U) (k % M)).imp_left fun hx => ?_
    rw [← neg_neg (arr _ _ _ _), neg_mem_light_neg] at hx
    exact ⟨_, hx, h _ (light_subset S M hx), (neg_neg _).symm⟩
  · exact .inr rfl

/-- For a light element `c`, the third array holds `-c` in the two cells below `2M` whose index is
congruent to `-c`. -/
theorem arrZ_of_light {c : ℤ} (hc : c ∈ light S M) (U : ℕ) {k : ℕ} (hk : k < 2 * M)
    (hkc : ((k % M : ℕ) : ℤ) = -c % (M : ℤ)) : arrZ S M U k = -c := by
  rw [arrZ, if_pos hk]
  exact arr_of_light ((neg_mem_light_neg S M c).mpr hc) _ hkc

/-- The padding value has absolute value `2U + 1`. -/
theorem abs_pad (U : ℕ) : |pad U| = 2 * (U : ℤ) + 1 :=
  abs_of_nonneg (by unfold pad; positivity)

/-- The entries of the array made from the first or the second set of a node have absolute value at
most `2U + 1`. -/
theorem abs_arrXY_le (M : ℕ) (h : Bdd U S) (i : ℕ) : |arrXY S M U i| ≤ 2 * (U : ℤ) + 1 := by
  rcases arrXY_cases M h i with ⟨-, hb⟩ | he
  · exact hb.trans (by omega)
  · rw [he, abs_pad]

/-- The entries of the third array of a node have absolute value at most `2U + 1`. -/
theorem abs_arrZ_le (M : ℕ) (h : Bdd U S) (k : ℕ) : |arrZ S M U k| ≤ 2 * (U : ℤ) + 1 := by
  rcases arrZ_cases M h k with ⟨c, -, hb, he⟩ | he
  · rw [he, abs_neg]
    exact hb.trans (by omega)
  · rw [he, abs_neg, abs_pad]

end cells

/-! ## One node -/

/-- **Correctness of one node.**  Its Convolution-3SUM instance, read at any length `N ≥ 2M`, has a
solution iff the light elements of the three sets have a 3SUM solution. -/
theorem node_correct {U M N : ℕ} (hM : 1 ≤ M) (hN : 2 * M ≤ N) {S₁ S₂ S₃ : Finset ℤ}
    (h₁ : Bdd U S₁) (h₂ : Bdd U S₂) (h₃ : Bdd U S₃) :
    ConvSol N (arrXY S₁ M U) (arrXY S₂ M U) (arrZ S₃ M U) ↔
      HasSol (light S₁ M) (light S₂ M) (light S₃ M) := by
  constructor
  · rintro ⟨i, j, -, heq⟩
    rcases arrXY_cases M h₁ i with ⟨ha, ha'⟩ | ha <;>
      rcases arrXY_cases M h₂ j with ⟨hb, hb'⟩ | hb <;>
      rcases arrZ_cases M h₃ (i + j) with ⟨c, hc, hc', hz⟩ | hz
    · exact ⟨_, ha, _, hb, c, hc, by rw [heq, hz]; ring⟩
    -- in all other cases a cell holds `±(2U + 1)`, which the other two cells cannot balance
    all_goals
      simp only [pad, abs_le] at *
      omega
  · rintro ⟨a, ha, b, hb, c, hc, hsum⟩
    have hM0 : (M : ℤ) ≠ 0 := by omega
    obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg a hM0)
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg b hM0)
    have := Int.emod_lt_of_pos a (by omega : (0 : ℤ) < M)
    have := Int.emod_lt_of_pos b (by omega : (0 : ℤ) < M)
    have hij : (((i + j) % M : ℕ) : ℤ) = -c % (M : ℤ) := by
      push_cast
      rw [← hi, ← hj, ← Int.add_emod]
      congr 1
      omega
    refine ⟨i, j, by omega, ?_⟩
    rw [arrXY, arr_of_light ha _ hi.symm, arrXY, arr_of_light hb _ hj.symm,
      arrZ_of_light hc U (by omega) hij]
    omega

/-! ## The sizes of the sets along the recursion -/

/-- The sequence `d₀ = 1`, `d_{j+1} = 2 d_j²` of [CH20], in closed form. -/
def dSeq (j : ℕ) : ℕ := 2 ^ (2 ^ j - 1)

/-- The recurrence `d_{j+1} = 2 d_j²`. -/
theorem dSeq_succ (j : ℕ) : dSeq (j + 1) = 2 * dSeq j ^ 2 := by
  have hexp : 2 ^ (j + 1) - 1 = 1 + (2 ^ j - 1) * 2 := by
    have := Nat.one_le_two_pow (n := j)
    rw [pow_succ]
    omega
  rw [dSeq, dSeq, hexp, pow_add, pow_mul, pow_one]

/-- The sequence `dSeq` is nondecreasing. -/
theorem dSeq_mono {i j : ℕ} (h : i ≤ j) : dSeq i ≤ dSeq j :=
  Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) h) 1)

/-- `d_h > n` at `h = height n`. -/
theorem lt_dSeq_height (n : ℕ) : n < dSeq (height n) := by
  have : Nat.log 2 n + 2 ≤ 2 ^ height n := Nat.le_pow_clog (by norm_num) _
  calc n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    _ ≤ dSeq (height n) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `height n` is at least 1, so the subtraction in `fuel` does not truncate. -/
theorem height_pos (n : ℕ) : 1 ≤ height n :=
  Nat.clog_pos (b := 2) (n := Nat.log 2 n + 2) (by norm_num) (by omega)

/-- `2^(height n) ≤ 2⌊log₂ n⌋ + 2`. -/
theorem two_pow_height_le (n : ℕ) : 2 ^ height n ≤ 2 * Nat.log 2 n + 2 := by
  have : 2 ^ (height n - 1) < Nat.log 2 n + 2 :=
    Nat.pow_pred_clog_lt_self (b := 2) (x := Nat.log 2 n + 2) (by norm_num) (by omega)
  rw [← Nat.sub_add_cancel (height_pos n), pow_succ]
  omega

/-- What is known about a set `T` that has been replaced `j` times by its heavy elements: its
elements have absolute value at most `U`, and there are at most `n / d_j` of them. -/
structure Replaced (n U j : ℕ) (T : Finset ℤ) : Prop where
  /-- The elements have absolute value at most `U`. -/
  bdd : Bdd U T
  /-- There are at most `n / d_j` elements. -/
  card : #T * dSeq j ≤ n

namespace Replaced

variable {n U j : ℕ} {T : Finset ℤ}

/-- At the root no set has been replaced. -/
theorem zero (hb : Bdd U T) (hc : #T ≤ n) : Replaced n U 0 T :=
  ⟨hb, by rwa [dSeq, pow_zero, Nat.sub_self, pow_zero, mul_one]⟩

/-- One more replacement: if at most `|T|²/(2n)` elements of `T` are heavy, then these are at most
`n / d_{j+1}`. -/
theorem heavy (h : Replaced n U j T) (hn : 1 ≤ n) {M : ℕ}
    (hM : 2 * n * #(ChanHe.heavy T M) ≤ #T ^ 2) : Replaced n U (j + 1) (ChanHe.heavy T M) := by
  refine ⟨h.bdd.mono (heavy_subset T M), Nat.le_of_mul_le_mul_left ?_ hn⟩
  calc n * (#(ChanHe.heavy T M) * dSeq (j + 1))
      = 2 * n * #(ChanHe.heavy T M) * dSeq j ^ 2 := by rw [dSeq_succ]; ring
    _ ≤ #T ^ 2 * dSeq j ^ 2 := Nat.mul_le_mul_right _ hM
    _ = #T * dSeq j * (#T * dSeq j) := by ring
    _ ≤ n * n := Nat.mul_le_mul h.card h.card

/-- After `height n` replacements a set is empty. -/
theorem eq_empty (h : Replaced n U j T) (hj : height n ≤ j) : T = ∅ := by
  by_contra hne
  have hcard : 1 ≤ #T := card_pos.mpr (nonempty_iff_ne_empty.mpr hne)
  -- `n < d_{height n} ≤ d_j ≤ |T| d_j ≤ n`
  have := lt_dSeq_height n
  have := dSeq_mono hj
  have := Nat.mul_le_mul_right (dSeq j) hcard
  have := h.card
  omega

end Replaced

/-- After `3 (height n) - 2` replacements in all, one of the three sets is empty. -/
theorem exists_eq_empty {n U j₁ j₂ j₃ : ℕ} {T₁ T₂ T₃ : Finset ℤ} (r₁ : Replaced n U j₁ T₁)
    (r₂ : Replaced n U j₂ T₂) (r₃ : Replaced n U j₃ T₃) (hj : 3 * height n - 2 ≤ j₁ + j₂ + j₃) :
    T₁ = ∅ ∨ T₂ = ∅ ∨ T₃ = ∅ := by
  have := height_pos n
  rcases (by omega : height n ≤ j₁ ∨ height n ≤ j₂ ∨ height n ≤ j₃) with h | h | h
  · exact .inl (r₁.eq_empty h)
  · exact .inr (.inl (r₂.eq_empty h))
  · exact .inr (.inr (r₃.eq_empty h))

/-! ## The recursion tree -/

/-- A solution stays a solution when the sets grow. -/
theorem HasSol.mono {S₁ S₂ S₃ T₁ T₂ T₃ : Finset ℤ} (h : HasSol S₁ S₂ S₃) (h₁ : S₁ ⊆ T₁)
    (h₂ : S₂ ⊆ T₂) (h₃ : S₃ ⊆ T₃) : HasSol T₁ T₂ T₃ :=
  let ⟨a, ha, b, hb, c, hc, hs⟩ := h
  ⟨a, h₁ ha, b, h₂ hb, c, h₃ hc, hs⟩

/-- If one of the three sets is empty there is no solution. -/
theorem not_hasSol_of_empty {S₁ S₂ S₃ : Finset ℤ} (h : S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅) :
    ¬ HasSol S₁ S₂ S₃ := by
  rintro ⟨a, ha, b, hb, c, hc, -⟩
  rcases h with rfl | rfl | rfl <;> simp_all

/-- A solution consists of three light elements, or it contains a heavy one.  The brackets are those
of the list of the children in `nodes`. -/
theorem hasSol_split (S₁ S₂ S₃ : Finset ℤ) (M : ℕ) :
    HasSol S₁ S₂ S₃ ↔ HasSol (light S₁ M) (light S₂ M) (light S₃ M) ∨
      (HasSol (heavy S₁ M) S₂ S₃ ∨ HasSol S₁ (heavy S₂ M) S₃) ∨ HasSol S₁ S₂ (heavy S₃ M) := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hs⟩
    by_contra hno
    simp only [not_or] at hno
    obtain ⟨hlight, ⟨hheavy₁, hheavy₂⟩, hheavy₃⟩ := hno
    exact hlight ⟨a, mem_sdiff.mpr ⟨ha, fun h => hheavy₁ ⟨a, h, b, hb, c, hc, hs⟩⟩,
      b, mem_sdiff.mpr ⟨hb, fun h => hheavy₂ ⟨a, ha, b, h, c, hc, hs⟩⟩,
      c, mem_sdiff.mpr ⟨hc, fun h => hheavy₃ ⟨a, ha, b, hb, c, h, hs⟩⟩, hs⟩
  · rintro (h | (h | h) | h)
    · exact h.mono (light_subset _ _) (light_subset _ _) (light_subset _ _)
    · exact h.mono (heavy_subset _ _) Subset.rfl Subset.rfl
    · exact h.mono Subset.rfl (heavy_subset _ _) Subset.rfl
    · exact h.mono Subset.rfl Subset.rfl (heavy_subset _ _)

/-- The first `f` levels of the tree have at most `(3^f - 1)/2` nodes. -/
theorem length_nodes_le (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    2 * (nodes Q Λ f S₁ S₂ S₃).length + 1 ≤ 3 ^ f := by
  induction f generalizing S₁ S₂ S₃ with
  | zero => simp [nodes]
  | succ f ih =>
    unfold nodes
    split_ifs with h
    · exact Nat.one_le_pow _ _ (by norm_num)
    · simp only [List.length_cons, List.length_append]
      have := ih (heavy S₁ (modulus Q Λ S₁ S₂ S₃)) S₂ S₃
      have := ih S₁ (heavy S₂ (modulus Q Λ S₁ S₂ S₃)) S₃
      have := ih S₁ S₂ (heavy S₃ (modulus Q Λ S₁ S₂ S₃))
      rw [pow_succ]
      omega

/-- The sets of a node are subsets of the sets at the root. -/
theorem nodes_subset (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    ∀ ν ∈ nodes Q Λ f S₁ S₂ S₃, ν.S₁ ⊆ S₁ ∧ ν.S₂ ⊆ S₂ ∧ ν.S₃ ⊆ S₃ := by
  induction f generalizing S₁ S₂ S₃ with
  | zero => simp [nodes]
  | succ f ih =>
    intro ν hν
    unfold nodes at hν
    split_ifs at hν with he
    · simp at hν
    · simp only [List.mem_cons, List.mem_append] at hν
      rcases hν with rfl | (hν | hν) | hν
      · exact ⟨Subset.rfl, Subset.rfl, Subset.rfl⟩
      · obtain ⟨s₁, s₂, s₃⟩ := ih _ _ _ ν hν
        exact ⟨s₁.trans (heavy_subset _ _), s₂, s₃⟩
      · obtain ⟨s₁, s₂, s₃⟩ := ih _ _ _ ν hν
        exact ⟨s₁, s₂.trans (heavy_subset _ _), s₃⟩
      · obtain ⟨s₁, s₂, s₃⟩ := ih _ _ _ ν hν
        exact ⟨s₁, s₂, s₃.trans (heavy_subset _ _)⟩

/-- The hypotheses on the set `Q` of candidates for the two searches: primes, all at most `m`, and
enough of them for `card_heavy_modulus_le`. -/
structure Candidates (n U m : ℕ) (Q : Finset ℕ) : Prop where
  /-- The candidates are primes. -/
  prime : ∀ p ∈ Q, p.Prime
  /-- The candidates are at most `m`. -/
  le : ∀ p ∈ Q, p ≤ m
  /-- There are at least `√(18n) Λ` candidates. -/
  card : 18 * Lam U ^ 2 * n ≤ #Q ^ 2

/-- The primes up to `mPar n U`, among which `reduction n U` searches, meet the hypotheses. -/
theorem candidates_primesLE (n U : ℕ) :
    Candidates n U (mPar n U) (Nat.primesLE (mPar n U)) :=
  ⟨fun _ => Nat.prime_of_mem_primesLE, fun _ => Nat.le_of_mem_primesLE,
    le_card_primesLE_mPar_sq n U⟩

/-- The induction behind `reduction_correct`.  If the `i`-th set has been replaced `j_i` times, then
`f` levels of the tree are enough as soon as `f + j₁ + j₂ + j₃ ≥ 3 (height n) - 2`. -/
theorem nodes_correct {n U N m : ℕ} (hn : 1 ≤ n) {Q : Finset ℕ} (hQ : Candidates n U m Q)
    (hN : 2 * m ^ 2 ≤ N) (f : ℕ) {T₁ T₂ T₃ : Finset ℤ} {j₁ j₂ j₃ : ℕ} (r₁ : Replaced n U j₁ T₁)
    (r₂ : Replaced n U j₂ T₂) (r₃ : Replaced n U j₃ T₃)
    (hf : 3 * height n - 2 ≤ f + j₁ + j₂ + j₃) :
    HasSol T₁ T₂ T₃ ↔ ∃ ν ∈ nodes Q (Lam U) f T₁ T₂ T₃, ν.Conv U N := by
  induction f generalizing T₁ T₂ T₃ j₁ j₂ j₃ with
  | zero => simp [nodes, not_hasSol_of_empty (exists_eq_empty r₁ r₂ r₃ (by omega))]
  | succ f ih =>
    unfold nodes
    split_ifs with he
    · simp [not_hasSol_of_empty he]
    obtain ⟨hM1, hMm⟩ := modulus_bounds (nonempty_of_le_card_sq hQ.card hn) hQ.prime hQ.le
      r₁.bdd r₂.bdd r₃.bdd
    have hheavy := card_heavy_modulus_le hQ.prime hQ.card hn r₁.bdd r₂.bdd r₃.bdd
    generalize modulus Q (Lam U) T₁ T₂ T₃ = M at hM1 hMm hheavy ⊢
    -- the node itself treats the light elements, and its three children the heavy ones
    have hnode := node_correct (N := N) hM1 (by omega) r₁.bdd r₂.bdd r₃.bdd
    have hchild₁ := ih (r₁.heavy hn (hheavy T₁ (by simp))) r₂ r₃ (by omega)
    have hchild₂ := ih r₁ (r₂.heavy hn (hheavy T₂ (by simp))) r₃ (by omega)
    have hchild₃ := ih r₁ r₂ (r₃.heavy hn (hheavy T₃ (by simp))) (by omega)
    rw [hasSol_split T₁ T₂ T₃ M, ← hnode, hchild₁, hchild₂, hchild₃]
    simp only [List.mem_cons, List.mem_append, or_and_right, exists_or, exists_eq_left]
    -- `Node.Conv` of the new node is by definition the instance of `node_correct`
    rfl

/-! ## The reduction for three sets -/

/-- The hypotheses on an input of `reduction n U`: each of the three sets has at most `n` elements,
all of absolute value at most `U`. -/
structure Admissible (n U : ℕ) (S₁ S₂ S₃ : Finset ℤ) : Prop where
  /-- The first set has at most `n` elements. -/
  card₁ : #S₁ ≤ n
  /-- The second set has at most `n` elements. -/
  card₂ : #S₂ ≤ n
  /-- The third set has at most `n` elements. -/
  card₃ : #S₃ ≤ n
  /-- The elements of the first set have absolute value at most `U`. -/
  bdd₁ : Bdd U S₁
  /-- The elements of the second set have absolute value at most `U`. -/
  bdd₂ : Bdd U S₂
  /-- The elements of the third set have absolute value at most `U`. -/
  bdd₃ : Bdd U S₃

/-- The sets of a node satisfy the hypotheses that the sets at the root satisfy. -/
theorem Admissible.of_mem {n U : ℕ} {S₁ S₂ S₃ : Finset ℤ} (h : Admissible n U S₁ S₂ S₃) {ν : Node}
    (hν : ν ∈ reduction n U S₁ S₂ S₃) : Admissible n U ν.S₁ ν.S₂ ν.S₃ :=
  let ⟨s₁, s₂, s₃⟩ := nodes_subset _ _ _ _ _ _ ν hν
  ⟨(card_le_card s₁).trans h.card₁, (card_le_card s₂).trans h.card₂,
    (card_le_card s₃).trans h.card₃, h.bdd₁.mono s₁, h.bdd₂.mono s₂, h.bdd₃.mono s₃⟩

/-- **Correctness of the reduction for three sets.**  Let the three sets have at most `n ≥ 1`
elements each, all of absolute value at most `U`, and let `N ≥ 2 * mPar n U ^ 2`.  Then 3SUM has a
solution iff the Convolution-3SUM instance of some node has one at length `N`. -/
theorem reduction_correct {n U N : ℕ} (hn : 1 ≤ n) (hN : 2 * mPar n U ^ 2 ≤ N)
    {S₁ S₂ S₃ : Finset ℤ} (h : Admissible n U S₁ S₂ S₃) :
    HasSol S₁ S₂ S₃ ↔ ∃ ν ∈ reduction n U S₁ S₂ S₃, ν.Conv U N :=
  nodes_correct hn (candidates_primesLE n U) hN (fuel n) (.zero h.bdd₁ h.card₁)
    (.zero h.bdd₂ h.card₂) (.zero h.bdd₃ h.card₃) le_rfl

/-- A ternary tree with `fuel n` levels has polylogarithmically many nodes. -/
theorem three_pow_fuel_le (n : ℕ) : 3 ^ fuel n ≤ (2 * Nat.log 2 n + 2) ^ 5 :=
  calc 3 ^ fuel n ≤ 3 ^ (3 * height n) := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    _ = 27 ^ height n := by rw [pow_mul]; norm_num
    _ ≤ 32 ^ height n := Nat.pow_le_pow_left (by norm_num) _
    _ = (2 ^ height n) ^ 5 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ (2 * Nat.log 2 n + 2) ^ 5 := Nat.pow_le_pow_left (two_pow_height_le n) 5

end ChanHe

end ThreeSumApsp
