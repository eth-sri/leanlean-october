/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
import CCDN.Analysis.GeometricShells
public import Mertens

/-!
Uniform prime-weighted reciprocal tails and degree cutoffs.

The Mertens lower bound for the prime sum after excluding a finite
bad-prime set.
-/

@[expose] public section
namespace CCDN
open Finset Real

/-- The explicit constant `log 4 + 6 + E₁` in Mertens' first theorem: for every `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ mertensError` (`Mertens.prime_sum_bounded_error`). -/
noncomputable def mertensError : ℝ := Real.log 4 + 6 + Mertens.E₁

/-- The Mertens error constant `mertensError` is positive. -/
lemma mertensError_pos : 0 < mertensError := by
  have hE : 0 ≤ Mertens.E₁ := tsum_nonneg Mertens.E₁.summand_nonneg
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertensError
  linarith

/-- The first Mertens estimate retains an explicit charge for excluded primes. -/
theorem prime_sum_lower_sdiff {x : ℝ} (hx : 1 ≤ x) (B : Finset ℕ) :
    Real.log x - mertensError - (∑ p ∈ B, Real.log p / p) ≤
      ∑ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, Real.log p / p := by
  let S := (Ioc 0 ⌊x⌋₊).filter Nat.Prime
  have hm := (abs_le.mp (Mertens.prime_sum_bounded_error hx)).1
  have he := sum_inter_add_sum_sdiff S B (fun p : ℕ => Real.log p / p)
  have hB : (∑ p ∈ S ∩ B, Real.log p / p) ≤ ∑ p ∈ B, Real.log p / p := by
    apply sum_le_sum_of_subset_of_nonneg inter_subset_right
    intro p _ _
    positivity
  change -mertensError ≤ (∑ p ∈ S, Real.log p / p) - Real.log x at hm
  linarith

end CCDN

namespace CCDN
noncomputable section
open Finset Real

/-- For `t ≥ 0`, a prime `p` lies in the set of primes in `(0, ⌊t⌋]` if and only if
`p ≤ t`. -/
lemma prime_mem_upto_iff {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : p.Prime) :
    p ∈ ((Ioc 0 ⌊t⌋₊).filter Nat.Prime) ↔ (p : ℝ) ≤ t := by
  simp only [mem_filter, mem_Ioc, hp, and_true, hp.pos, true_and]
  exact Nat.le_floor_iff ht

/-- An explicit constant bounding the prime weight `∑ log p / p` over the primes in any
interval `(L, 4 L]` with `L ≥ 1`. -/
def primeBlockMass : ℝ := Real.log 4 + 2 * mertensError

/-- The prime block constant `primeBlockMass` is positive. -/
lemma primeBlockMass_pos : 0 < primeBlockMass := by
  have h := mertensError_pos
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  dsimp [primeBlockMass]
  linarith

section

variable (n : ℕ) {L : ℝ} (hL : 1 ≤ L) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hlo : ∀ p ∈ S, L < (p : ℝ)) (hhi : ∀ p ∈ S, (p : ℝ) ≤ 4 * L)

include hL hprime hlo hhi in
/-- The Mertens bounded error bounds every factor-four prime interval by a
constant independent of its location. -/
private lemma prime_block_weight_le :
    ∑ p ∈ S, Real.log p / p ≤ primeBlockMass := by
  let T := (Ioc 0 ⌊4 * L⌋₊).filter Nat.Prime
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  have hUT : U ⊆ T := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    apply (prime_mem_upto_iff (by linarith) hp').mpr
    linarith [(prime_mem_upto_iff (by linarith) hp').mp hp]
  have hST : S ⊆ T \ U := by
    intro p hp
    apply mem_sdiff.mpr
    refine ⟨(prime_mem_upto_iff (by linarith) (hprime p hp)).mpr (hhi p hp), ?_⟩
    intro hu
    exact (not_le_of_gt (hlo p hp)) ((prime_mem_upto_iff (by linarith) (hprime p hp)).mp hu)
  have hs : (∑ p ∈ S, Real.log p / p) ≤ ∑ p ∈ T \ U, Real.log p / p :=
    by gcongr
  have hsplit := sum_sdiff hUT (f := fun p : ℕ => Real.log p / p)
  have hlo' := (abs_le.mp (Mertens.prime_sum_bounded_error hL)).1
  have hhi' := (abs_le.mp (Mertens.prime_sum_bounded_error (by linarith : 1 ≤ 4 * L))).2
  change -mertensError ≤ (∑ p ∈ U, Real.log p / p) - Real.log L at hlo'
  change (∑ p ∈ T, Real.log p / p) - Real.log (4 * L) ≤ mertensError at hhi'
  rw [Real.log_mul (by norm_num) (by linarith)] at hhi'
  dsimp only [primeBlockMass]
  linarith

include hL hprime hlo hhi in
/-- A prime interval above L has weighted reciprocal-square-root mass
bounded by its Mertens weight divided by sqrt(L). -/
private lemma prime_block_sqrt_weight_le :
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

include hL hprime hlo in
theorem prime_sqrt_tail_le : ∑ p ∈ S, Real.log p / p / Real.sqrt p ≤ 2 * primeBlockMass / Real.sqrt L := by
  have hpos : 0 < L := by linarith
  apply (geometric_shell_sum S (fun p => p/L) _ (r:=4) (M:=primeBlockMass/Real.sqrt L) (by norm_num)
    (div_nonneg primeBlockMass_pos.le (sqrt_nonneg _)) (fun p h => (one_lt_div hpos).mpr (hlo p h)) ?_).trans_eq (by ring)
  intro k T hT band
  have h4 : (1:ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
  have hh := prime_block_sqrt_weight_le (one_le_mul_of_one_le_of_one_le h4 hL) T (fun i h => hprime i (hT h))
    (fun i h => (lt_div_iff₀ hpos).mp (band i h).1) (fun i h => by have := (div_le_iff₀ hpos).mp (band i h).2; rw [pow_succ] at this; linarith)
  apply hh.trans_eq
  rw [sqrt_mul (by positivity),show (4:ℝ)^k = (2^k)^2 by rw [← pow_mul, mul_comm k, pow_mul]; norm_num,sqrt_sq (by positivity),one_div,inv_pow]; ring

end

/-- The exact reciprocal perturbation error, retaining the prime weight
needed for the sharp tail estimate. -/
private lemma log_div_sqrt_perturbation_exact {p C N : ℝ} (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hN : 0 < N) (hupper : N ≤ p + C * Real.sqrt p) :
    Real.log p / p - C * (Real.log p / p / Real.sqrt p) ≤ Real.log p / N := by
  have hp0 : 0 < p := by linarith
  have hs0 := Real.sqrt_pos.mpr hp0
  have hs := Real.sq_sqrt hp0.le
  have hrec : 1 / p - C / (p * Real.sqrt p) ≤ 1 / (p + C * Real.sqrt p) := by
    apply (le_div_iff₀ (by positivity)).mpr
    field_simp
    nlinarith [sq_nonneg C]
  calc _ = Real.log p * (1 / p - C / (p * Real.sqrt p)) := by ring
       _ ≤ Real.log p * (1 / (p + C * Real.sqrt p)) := (mul_le_mul_of_nonneg_left hrec (Real.log_nonneg hp))
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
  let S := (T \ B).filter (fun p : ℕ => L < p)
  have hS : S = T \ (B ∪ U) := by
    ext p
    by_cases hp : p ∈ T
    · have hU : p ∈ U ↔ (p : ℝ) ≤ L := prime_mem_upto_iff (by linarith) ((mem_filter.mp hp).2)
      grind
    grind
  have hcharge : (∑ p ∈ B ∪ U, Real.log p / p) ≤
      (∑ p ∈ B, Real.log p / p) + (∑ p ∈ U, Real.log p / p) := by
    have he := sum_union_inter (s₁ := B) (s₂ := U) (f := fun p : ℕ => Real.log p / p)
    have hn : 0 ≤ ∑ p ∈ B ∩ U, Real.log p / p := by positivity
    linarith
  have hu := (abs_le.mp (Mertens.prime_sum_bounded_error hL)).2
  change (∑ p ∈ U, Real.log p / p) - Real.log L ≤ mertensError at hu
  have hm := prime_sum_lower_sdiff hx (B ∪ U)
  rw [← hS] at hm
  have hprime (p : ℕ) (hp : p ∈ S)  :=
    (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).1).1).2
  have htail := prime_sqrt_tail_le hL S hprime (by grind)
  have hpoint : ∀ p ∈ S, Real.log p / p - C * (Real.log p / p / Real.sqrt p) ≤
      Real.log p / N p := by
    grind [mem_filter.mp, log_div_sqrt_perturbation_exact, one_le]
  have hs := sum_le_sum hpoint
  rw [sum_sub_distrib, ← mul_sum] at hs
  nlinarith

end
end CCDN
