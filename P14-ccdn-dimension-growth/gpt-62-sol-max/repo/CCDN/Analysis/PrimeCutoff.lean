/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mertens
import CCDN.Analysis.GeometricShells

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

noncomputable section

/-- Primes up to a real endpoint. -/
def primesUpTo (T : ℝ) : Finset ℕ := (Ioc 0 ⌊T⌋₊).filter Nat.Prime

lemma mem_primesUpTo {T : ℝ} {p : ℕ} :
    p ∈ primesUpTo T ↔ p.Prime ∧ (p : ℝ) ≤ T := by
  by_cases hT : 0 ≤ T
  · simp only [primesUpTo, mem_filter, mem_Ioc, Nat.le_floor_iff hT]
    grind [Nat.Prime.pos]
  · simp [primesUpTo, Nat.floor_of_nonpos (le_of_not_ge hT),
      show ¬(p : ℝ) ≤ T by linarith [Nat.cast_nonneg (α := ℝ) p]]

/-- Primes in the interval `(L, T]`. -/
def primesInInterval (L T : ℝ) : Finset ℕ := primesUpTo T \ primesUpTo L

lemma mem_primesInInterval {L T : ℝ} {p : ℕ} :
    p ∈ primesInInterval L T ↔ p.Prime ∧ L < (p : ℝ) ∧ (p : ℝ) ≤ T := by
  simp only [primesInInterval, mem_sdiff, mem_primesUpTo]
  grind

/-- The two-sided first Mertens estimate for an interval, obtained by subtraction. -/
lemma prime_interval_weight_bounds {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T) :
    let w := ∑ p ∈ primesInInterval L T, Real.log p / p
    Real.log T - Real.log L - 2 * mertensError ≤ w ∧
      w ≤ Real.log T - Real.log L + 2 * mertensError := by
  have hsub : primesUpTo L ⊆ primesUpTo T := fun p hp =>
    mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hp).1, (mem_primesUpTo.mp hp).2.trans hLT⟩
  have hsum := sum_sdiff hsub (f := fun p : ℕ => Real.log p / p)
  have h₁ : |(∑ p ∈ primesUpTo L, Real.log p / p) - Real.log L| ≤ mertensError :=
    Mertens.prime_sum_bounded_error hL
  have h₂ : |(∑ p ∈ primesUpTo T, Real.log p / p) - Real.log T| ≤ mertensError :=
    Mertens.prime_sum_bounded_error (hL.trans hLT)
  dsimp [primesInInterval]
  constructor <;> linarith only [hsum, (abs_le.mp h₁).1, (abs_le.mp h₁).2,
    (abs_le.mp h₂).1, (abs_le.mp h₂).2]

/-- Upper bound for the prime weight of any subset of an interval. -/
lemma prime_interval_weight_le {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hlo : ∀ p ∈ P, L < (p : ℝ))
    (hhi : ∀ p ∈ P, (p : ℝ) ≤ T) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log T - Real.log L + 2 * mertensError :=
  (sum_le_sum_of_subset_of_nonneg
    (fun p hp => mem_primesInInterval.mpr ⟨hP p hp, hlo p hp, hhi p hp⟩)
    (fun _ _ _ => by positivity)).trans (prime_interval_weight_bounds hL hLT).2

/-- An explicit constant bounding the prime weight `∑ log p / p` over the primes in any
interval `(L, 4 L]` with `L ≥ 1`. -/
def primeBlockMass : ℝ := Real.log 4 + 2 * mertensError

/-- The prime block constant `primeBlockMass` is positive. -/
lemma primeBlockMass_pos : 0 < primeBlockMass := by
  have h := mertensError_pos
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  grind [primeBlockMass]

/-- A prime interval above L has weighted reciprocal-square-root mass
bounded by its Mertens weight divided by sqrt(L). -/
private lemma prime_block_sqrt_weight_le {L : ℝ} (hL : 1 ≤ L) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hlo : ∀ p ∈ S, L < (p : ℝ))
    (hhi : ∀ p ∈ S, (p : ℝ) ≤ 4 * L) :
    ∑ p ∈ S, Real.log p / p / Real.sqrt p ≤ primeBlockMass / Real.sqrt L := by
  have hs : (∑ p ∈ S, Real.log p / p / Real.sqrt p) ≤
      (∑ p ∈ S, Real.log p / p) / Real.sqrt L := by
    rw [sum_div]
    apply sum_le_sum
    intro p hp
    exact div_le_div_of_nonneg_left (by positivity)
      (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt (hlo p hp).le)
  have h := prime_interval_weight_le hL (show L ≤ 4 * L by linarith) S hprime hlo hhi
  rw [Real.log_mul (by norm_num) (by linarith : L ≠ 0), add_sub_cancel_right] at h
  exact hs.trans (div_le_div_of_nonneg_right h (Real.sqrt_nonneg L))

/-- The reciprocal-square-root tail over any finite set of primes is uniform
in its upper endpoint. -/
theorem prime_sqrt_tail_le {L : ℝ} (hL : 1 ≤ L) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hlo : ∀ p ∈ S, L < (p : ℝ)) :
    ∑ p ∈ S, Real.log p / p / Real.sqrt p ≤ 2 * primeBlockMass / Real.sqrt L := by
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  have h := sum_le_of_geometric_shells S (fun p => (p : ℝ)) (fun p => log p / p / sqrt p)
    (L := L) (q := 4) (C := primeBlockMass / sqrt L) (D := 0) hL₀ (by norm_num)
    (by positivity [primeBlockMass_pos])
  rw [zero_add, ← mul_div_assoc] at h
  apply h
  · simp [filter_eq_empty_iff.mpr (fun p hp => (hlo p hp).not_ge)]
  · intro n
    let A := S.filter (fun p : ℕ => L * 4 ^ n < (p : ℝ) ∧ (p : ℝ) ≤ L * 4 ^ (n + 1))
    have h₁ : 1 ≤ L * (4 : ℝ) ^ n := by nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) (n := n)]
    have hb := prime_block_sqrt_weight_le h₁ A
      (fun p hp => hprime p (mem_filter.mp hp).1) (fun p hp => (mem_filter.mp hp).2.1)
      (fun p hp => by simpa [pow_succ, mul_left_comm, mul_comm, mul_assoc] using (mem_filter.mp hp).2.2)
    convert hb using 1
    have hs : sqrt ((4 : ℝ) ^ n) = 2 ^ n := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm, pow_mul, Real.sqrt_sq (by positivity)]
    simp [Real.sqrt_mul hL₀.le, hs, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The exact reciprocal perturbation error, retaining the prime weight
needed for the sharp tail estimate. -/
private lemma log_div_sqrt_perturbation_exact {p C : ℝ} (hp : 1 ≤ p) (hC : 0 ≤ C) :
    Real.log p / p - C * (Real.log p / p / Real.sqrt p) ≤
      Real.log p / (p + C * Real.sqrt p) := by
  have hp0 : 0 < p := by linarith
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hrec : 1 / p - C / (p * Real.sqrt p) ≤ 1 / (p + C * Real.sqrt p) := by
    apply (le_div_iff₀ (by positivity : 0 < p + C * Real.sqrt p)).mpr
    field_simp
    nlinarith [sq_nonneg C]
  have hlog := mul_le_mul_of_nonneg_left hrec (Real.log_nonneg hp)
  calc _ = Real.log p * (1 / p - C / (p * Real.sqrt p)) := by ring
       _ ≤ _ := by simpa only [mul_one_div] using hlog

/-- Good-prime reciprocal sum with an explicit lower cutoff. Its error is
O(C/sqrt(L)), with absolute constants, and its small-prime cost is log(L). -/
theorem weighted_prime_sum_lower_cutoff {x L C : ℝ} (hx : 1 ≤ x) (hL : 1 ≤ L)
    (hC : 0 ≤ C) (B : Finset ℕ) :
    Real.log x - Real.log L - 2 * mertensError - (∑ p ∈ B, Real.log p / p) -
      C * (2 * primeBlockMass / Real.sqrt L) ≤
      ∑ p ∈ primesInInterval L x \ B, Real.log p / (p + C * Real.sqrt p) := by
  classical
  let T := primesInInterval L x
  let S := T \ B
  have hbase : Real.log x - Real.log L - 2 * mertensError -
      (∑ p ∈ B, Real.log p / p) ≤ ∑ p ∈ S, Real.log p / p := by
    by_cases hLx : L ≤ x
    · have hsplit := sum_inter_add_sum_sdiff T B (fun p : ℕ => Real.log p / p)
      have hb := sum_le_sum_of_subset_of_nonneg (s := T ∩ B) inter_subset_right
        (f := fun p : ℕ => Real.log p / p) (fun _ _ _ => by positivity)
      linarith [(prime_interval_weight_bounds hL hLx).1]
    have hc := Real.log_le_log (by linarith : 0 < x) (le_of_not_ge hLx)
    have hp := mertensError_pos
    have hn (R : Finset ℕ) : 0 ≤ ∑ p ∈ R, Real.log p / p := sum_nonneg (fun _ _ => by positivity)
    linarith [hn B, hn S]
  have hm (p : ℕ) (hp : p ∈ S) := mem_primesInInterval.mp (mem_sdiff.mp hp).1
  have htail := prime_sqrt_tail_le hL S (fun p hp => (hm p hp).1) (fun p hp => (hm p hp).2.1)
  have hs := sum_le_sum (s := S) fun p hp =>
    log_div_sqrt_perturbation_exact (p := (p : ℝ)) (hL.trans (hm p hp).2.1.le) hC
  rw [sum_sub_distrib, ← mul_sum] at hs
  change _ ≤ ∑ p ∈ S, Real.log p / (p + C * Real.sqrt p)
  nlinarith

end
end CCDN
