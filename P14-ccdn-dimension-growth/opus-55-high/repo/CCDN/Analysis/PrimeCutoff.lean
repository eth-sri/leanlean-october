/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mertens

/-!
Uniform prime-weighted reciprocal tails and degree cutoffs.

The Mertens lower bound for the prime sum after excluding a finite
bad-prime set.
-/

namespace CCDN
open Finset Real

/-- The explicit constant `log 4 + 6 + E₁` in Mertens' first theorem: for every `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ mertensError` (`Mertens.prime_sum_bounded_error`). -/
noncomputable def mertensError : ℝ := Real.log 4 + 6 + Mertens.E₁

/-- The Mertens error constant `mertensError` is positive. -/
lemma mertensError_pos : 0 < mertensError := by
  have hE : 0 ≤ Mertens.E₁ := tsum_nonneg Mertens.E₁.summand_nonneg
  have hl : 0 ≤ Real.log 4 := by positivity
  unfold mertensError
  linarith

end CCDN

namespace CCDN
noncomputable section
open Finset Real

/-- For `t ≥ 0`, a prime `p` lies in the set of primes in `(0, ⌊t⌋]` if and only if
`p ≤ t`. -/
lemma prime_mem_upto_iff {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : p.Prime) :
    p ∈ ((Ioc 0 ⌊t⌋₊).filter Nat.Prime) ↔ (p : ℝ) ≤ t := by
  simp [mem_filter, mem_Ioc, hp, and_true, hp.pos, true_and]
  exact Nat.le_floor_iff ht

/-- An explicit constant bounding the prime weight `∑ log p / p` over the primes in any
interval `(L, 4 L]` with `L ≥ 1`. -/
def primeBlockMass : ℝ := Real.log 4 + 2 * mertensError

/-- The prime block constant `primeBlockMass` is positive. -/
lemma primeBlockMass_pos : 0 < primeBlockMass := by
  have h := mertensError_pos
  have hl : 0 ≤ Real.log 4 := by positivity
  dsimp [primeBlockMass]
  linarith

section
variable {L : ℝ} (hL : 1 ≤ L) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) (hlo : ∀ p ∈ S, L < (p : ℝ)) (hhi : ∀ p ∈ S, (p : ℝ) ≤ 4 * L)
include hL hprime hlo hhi

/-- The Mertens bounded error bounds every factor-four prime interval by a
constant independent of its location. -/
lemma prime_block_weight_le
    :
    ∑ p ∈ S, Real.log p / p ≤ primeBlockMass := by
  let T := (Ioc 0 ⌊4 * L⌋₊).filter Nat.Prime
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  have hUT : U ⊆ T := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    apply (prime_mem_upto_iff (by linarith) hp').mpr
    have hu := (prime_mem_upto_iff (by linarith) hp').mp hp
    linarith
  have hST : S ⊆ T \ U := by
    intro p hp
    apply mem_sdiff.mpr
    refine ⟨(prime_mem_upto_iff (by linarith) (hprime p hp)).mpr (hhi p hp), ?_⟩
    intro hu
    exact (not_le_of_gt (hlo p hp)) ((prime_mem_upto_iff (by linarith) (hprime p hp)).mp hu)
  have hs : (∑ p ∈ S, Real.log p / p) ≤ ∑ p ∈ T \ U, Real.log p / p :=
    sum_le_sum_of_subset_of_nonneg hST (fun p _ _ => by positivity)
  have hsplit := sum_sdiff hUT (f := fun p : ℕ => Real.log p / p)
  have hlo' := (abs_le.mp (Mertens.prime_sum_bounded_error hL)).1
  have hhi' := (abs_le.mp (Mertens.prime_sum_bounded_error (by linarith : 1 ≤ 4 * L))).2
  change -mertensError ≤ (∑ p ∈ U, Real.log p / p) - Real.log L at hlo'
  change (∑ p ∈ T, Real.log p / p) - Real.log (4 * L) ≤ mertensError at hhi'
  rw [Real.log_mul (by norm_num) (by grind)] at hhi'
  dsimp [primeBlockMass]
  linarith

/-- A prime interval above L has weighted reciprocal-square-root mass
bounded by its Mertens weight divided by sqrt(L). -/
lemma prime_block_sqrt_weight_le
    :
    ∑ p ∈ S, Real.log p / p / Real.sqrt p ≤ primeBlockMass / Real.sqrt L := by
  have hs : (∑ p ∈ S, Real.log p / p / Real.sqrt p) ≤
      (∑ p ∈ S, Real.log p / p) / Real.sqrt L := by
    rw [sum_div]
    apply sum_le_sum
    intro p hp
    exact div_le_div_of_nonneg_left (by positivity)
      (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt (hlo p hp).le)
  exact hs.trans (div_le_div_of_nonneg_right (prime_block_weight_le hL S hprime hlo hhi)
    (Real.sqrt_nonneg L))

end

section
variable {L : ℝ}

/-- Finite dyadic assembly retains a constant times L^(-1/2), rather than
summing over every integer and losing a logarithm. -/
lemma prime_sqrt_tail_le_of_pow_bound (n : ℕ) (hL : 1 ≤ L)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) (hlo : ∀ p ∈ S, L < (p : ℝ))
    (hhi : ∀ p ∈ S, (p : ℝ) ≤ 4 ^ n * L) :
    ∑ p ∈ S, Real.log p / p / Real.sqrt p ≤ 2 * primeBlockMass / Real.sqrt L := by
  induction n generalizing L S with
  | zero =>
    have hS : S = ∅ := by grind
    rw [hS, sum_empty]
    exact div_nonneg (mul_nonneg (by norm_num) primeBlockMass_pos.le) (Real.sqrt_nonneg _)
  | succ n ih =>
    let A := S.filter (fun p : ℕ => (p : ℝ) ≤ 4 * L)
    let B := S \ A
    have hA := prime_block_sqrt_weight_le hL A
      (fun p hp => hprime p (mem_filter.mp hp).1)
      (fun p hp => hlo p (mem_filter.mp hp).1) (fun _ hp => (mem_filter.mp hp).2)
    have hB := ih (L := 4 * L) (by linarith) B
      (fun p hp => hprime p (mem_sdiff.mp hp).1)
      (fun p hp => by grind)
      (fun p hp => by grind [pow_succ, mul_assoc])
    have he : ∑ p ∈ S, Real.log p / p / Real.sqrt p =
        (∑ p ∈ A, Real.log p / p / Real.sqrt p) +
        ∑ p ∈ B, Real.log p / p / Real.sqrt p := by
      simpa only [add_comm] using
        (sum_sdiff (filter_subset (fun p : ℕ => (p : ℝ) ≤ 4 * L) S)
          (f := fun p : ℕ => Real.log p / p / Real.sqrt p)).symm
    have hsqrt : Real.sqrt (4 * L) = 2 * Real.sqrt L := by
      norm_num
    rw [he]
    rw [hsqrt] at hB
    have hL0 : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
    calc _ ≤ primeBlockMass / Real.sqrt L + 2 * primeBlockMass / (2 * Real.sqrt L) :=
          add_le_add hA hB
         _ = _ := by grind

end

/-- The exact reciprocal perturbation error, retaining the prime weight
needed for the sharp tail estimate. -/
lemma log_div_sqrt_perturbation_exact {p C N : ℝ} (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hN : 0 < N) (hupper : N ≤ p + C * Real.sqrt p) :
    Real.log p / p - C * (Real.log p / p / Real.sqrt p) ≤ Real.log p / N := by
  have hp0 : 0 < p := by linarith
  have hs0 := Real.sqrt_pos.mpr hp0
  have hs := Real.sq_sqrt hp0.le
  have hrec : 1 / p - C / (p * Real.sqrt p) ≤ 1 / (p + C * Real.sqrt p) := by
    field_simp
    nlinarith [sq_nonneg C]
  have hlog := mul_le_mul_of_nonneg_left hrec (Real.log_nonneg hp)
  calc _ = Real.log p * (1 / p - C / (p * Real.sqrt p)) := by ring
       _ ≤ Real.log p * (1 / (p + C * Real.sqrt p)) := hlog
       _ ≤ _ := by
         rw [mul_one_div]
         bound

/-- Good-prime reciprocal sum with an explicit lower cutoff. Its error is
O(C/sqrt(L)), with absolute constants, and its small-prime cost is log(L). -/
theorem weighted_prime_sum_lower_cutoff {x L C : ℝ} (hx : 1 ≤ x) (hL : 1 ≤ L)
    (hC : 0 ≤ C) (B : Finset ℕ) (N : ℕ → ℝ)
    (hN : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) → 0 < N p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      N p ≤ p + C * Real.sqrt p) :
    Real.log x - Real.log L - 2 * mertensError - (∑ p ∈ B, Real.log p / p) -
      C * (2 * primeBlockMass / Real.sqrt L) ≤
      ∑ p ∈ (((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B).filter (fun p : ℕ => L < (p : ℝ)),
        Real.log p / N p := by
  classical
  let T := (Ioc 0 ⌊x⌋₊).filter Nat.Prime
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  let S := (T \ B).filter (fun p : ℕ => L < (p : ℝ))
  have hS : S = T \ (B ∪ U) := by
    ext p
    by_cases hp : p ∈ T
    · have hprime := (mem_filter.mp hp).2
      have hU : p ∈ U ↔ p ≤ L := prime_mem_upto_iff (by linarith) hprime
      grind
    grind
  have hcharge : (∑ p ∈ B ∪ U, Real.log p / p) ≤
      (∑ p ∈ B, Real.log p / p) + (∑ p ∈ U, Real.log p / p) := by
    have he := sum_union_inter (s₁ := B) (s₂ := U) (f := fun p => Real.log p / p)
    have hn : 0 ≤ ∑ p ∈ B ∩ U, Real.log p / p := sum_nonneg (fun _ _ => by positivity)
    linarith
  have hu := (abs_le.mp (Mertens.prime_sum_bounded_error hL)).2
  change (∑ p ∈ U, Real.log p / p) - Real.log L ≤ mertensError at hu
  have hm : Real.log x - mertensError - (∑ p ∈ (B ∪ U), Real.log p / p) ≤
      ∑ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ (B ∪ U), Real.log p / p := by
    let S := (Ioc 0 ⌊x⌋₊).filter Nat.Prime
    have hm := (abs_le.mp (Mertens.prime_sum_bounded_error hx)).1
    have he := sum_inter_add_sum_sdiff S (B ∪ U) (fun p => Real.log p / p)
    have hB : (∑ p ∈ S ∩ (B ∪ U), Real.log p / p) ≤ ∑ p ∈ (B ∪ U), Real.log p / p := by
      apply sum_le_sum_of_subset_of_nonneg inter_subset_right
      intro p _ _
      positivity
    change Real.log x - mertensError - _ ≤ ∑ p ∈ S \ (B ∪ U), Real.log p / p
    change -mertensError ≤ (∑ p ∈ S, Real.log p / p) - Real.log x at hm
    linarith
  change Real.log x - mertensError - _ ≤ ∑ p ∈ T \ (B ∪ U), Real.log p / p at hm
  rw [← hS] at hm
  have hbase : Real.log x - Real.log L - 2 * mertensError -
      (∑ p ∈ B, Real.log p / p) ≤ ∑ p ∈ S, Real.log p / p := by linarith
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime :=
    (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).1).1).2
  have htail : ∑ p ∈ S, Real.log p / p / Real.sqrt p ≤ 2 * primeBlockMass / Real.sqrt L := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((S.sup id : ℕ) : ℝ) / L)
      (by norm_num : (1 : ℝ) < 4)
    apply prime_sqrt_tail_le_of_pow_bound n hL S hprime (fun _ hp => (mem_filter.mp hp).2)
    intro p hp
    have hsup : p ≤ ((S.sup id : ℕ) : ℝ) := by
      exact_mod_cast (le_sup (f := id) hp : p ≤ S.sup id)
    exact hsup.trans ((div_lt_iff₀ (by grind)).mp hn).le
  have hpoint : ∀ p ∈ S, Real.log p / p - C * (Real.log p / p / Real.sqrt p) ≤
      Real.log p / N p := by
    intro p hp
    have hmem := mem_filter.mp hp
    exact log_div_sqrt_perturbation_exact (mod_cast (hprime p hp).one_le) hC
      (hN p hmem.1 hmem.2) (hupper p hmem.1 hmem.2)
  have hs := sum_le_sum hpoint
  rw [sum_sub_distrib, ← mul_sum] at hs
  nlinarith

