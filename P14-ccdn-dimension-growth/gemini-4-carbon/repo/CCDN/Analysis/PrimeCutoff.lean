/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mertens

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

def mertensError : ℝ := Real.log 4 + 12

lemma mertensError_pos : 0 < mertensError := by
  unfold mertensError; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]

lemma prime_mem_upto_iff {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : p.Prime) :
    p ∈ ((Ioc 0 ⌊t⌋₊).filter Nat.Prime) ↔ (p : ℝ) ≤ t := by
  simp only [mem_filter, mem_Ioc, hp, and_true, hp.pos, true_and]
  exact Nat.le_floor_iff ht

lemma prime_interval_weight_le {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hlo : ∀ p ∈ P, L < (p : ℝ)) (hhi : ∀ p ∈ P, (p : ℝ) ≤ T) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log T - Real.log L + 2 * mertensError := by
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  let V := (Ioc 0 ⌊T⌋₊).filter Nat.Prime
  have hUV : U ⊆ V := fun p hp => (prime_mem_upto_iff (by linarith) (mem_filter.mp hp).2).mpr
    (((prime_mem_upto_iff (by linarith) (mem_filter.mp hp).2).mp hp).trans hLT)
  have hPV : P ⊆ V \ U := fun p hp => mem_sdiff.mpr
    ⟨(prime_mem_upto_iff (by linarith) (hP p hp)).mpr (hhi p hp), fun hu =>
      (hlo p hp).not_ge ((prime_mem_upto_iff (by linarith) (hP p hp)).mp hu)⟩
  have hsum := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log p / p) hPV fun _ _ _ =>
    by positivity
  have hsplit := sum_sdiff hUV (f := fun p : ℕ => Real.log p / p)
  have hl := (abs_le.mp (Mertens.prime_sum_bounded_error hL)).1
  have ht := (abs_le.mp (Mertens.prime_sum_bounded_error (hL.trans hLT))).2
  change -mertensError ≤ (∑ p ∈ U, Real.log p / p) - Real.log L at hl
  change (∑ p ∈ V, Real.log p / p) - Real.log T ≤ mertensError at ht
  linarith

def primeBlockMass : ℝ := Real.log 4 + 2 * mertensError

lemma primeBlockMass_pos : 0 < primeBlockMass := by
  unfold primeBlockMass; linarith [mertensError_pos, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]

private lemma prime_sqrt_tail_le_of_pow_bound (n : ℕ) {L : ℝ} (hL : 1 ≤ L)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) (hlo : ∀ p ∈ S, L < (p : ℝ))
    (hhi : ∀ p ∈ S, (p : ℝ) ≤ 4 ^ n * L) :
    ∑ p ∈ S, Real.log p / p / Real.sqrt p ≤ 2 * primeBlockMass / Real.sqrt L := by
  induction n generalizing L S with
  | zero =>
    rw [eq_empty_iff_forall_notMem (s := S) |>.mpr fun p hp => by
      have := hlo p hp; have := hhi p hp; simp only [pow_zero, one_mul] at this; linarith, sum_empty]
    exact div_nonneg (mul_nonneg (by norm_num) primeBlockMass_pos.le) (Real.sqrt_nonneg _)
  | succ n ih =>
    let A := S.filter (fun p : ℕ => (p : ℝ) ≤ 4 * L)
    have hA : ∑ p ∈ A, Real.log p / p / Real.sqrt p ≤ primeBlockMass / Real.sqrt L := by
      refine (sum_le_sum fun p hp => div_le_div_of_nonneg_left (by positivity)
        (Real.sqrt_pos.mpr (by linarith))
        (Real.sqrt_le_sqrt (hlo p (mem_filter.mp hp).1).le)).trans ?_
      rw [← sum_div]
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg L)
      have hw := prime_interval_weight_le hL (by linarith : L ≤ 4 * L) A
        (fun p hp => hprime p (mem_filter.mp hp).1)
        (fun p hp => hlo p (mem_filter.mp hp).1) (fun _ hp => (mem_filter.mp hp).2)
      rw [Real.log_mul (by norm_num) (by linarith)] at hw
      unfold primeBlockMass; linarith
    have hB := ih (L := 4 * L) (by linarith) (S \ A)
      (fun p hp => hprime p (mem_sdiff.mp hp).1)
      (fun p hp => lt_of_not_ge fun hn => (mem_sdiff.mp hp).2 (mem_filter.mpr ⟨(mem_sdiff.mp hp).1, hn⟩))
      (fun p hp => by simpa only [pow_succ, mul_assoc] using hhi p (mem_sdiff.mp hp).1)
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]] at hB
    rw [← sum_sdiff (filter_subset (fun p : ℕ => (p : ℝ) ≤ 4 * L) S)]
    have hL0 : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    calc _ ≤ 2 * primeBlockMass / (2 * Real.sqrt L) + primeBlockMass / Real.sqrt L := add_le_add hB hA
      _ = _ := by field_simp; ring

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
    · have hU : p ∈ U ↔ (p : ℝ) ≤ L := prime_mem_upto_iff (by linarith) (mem_filter.mp hp).2
      simp only [S, mem_filter, mem_sdiff, mem_union, hp, true_and, hU, not_or, not_le]
    · simp [S, hp]
  have hcharge : (∑ p ∈ T ∩ (B ∪ U), Real.log p / p) ≤
      (∑ p ∈ B, Real.log p / p) + (∑ p ∈ U, Real.log p / p) :=
    (sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log p / p)
      inter_subset_right fun _ _ _ => by positivity).trans
      (by linarith [sum_union_inter (s₁ := B) (s₂ := U) (f := fun p : ℕ => Real.log p / p),
        sum_nonneg (s := B ∩ U) fun (p : ℕ) _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)])
  have hu := (abs_le.mp (Mertens.prime_sum_bounded_error hL)).2
  have hx' := (abs_le.mp (Mertens.prime_sum_bounded_error hx)).1
  change (∑ p ∈ U, Real.log p / p) - Real.log L ≤ mertensError at hu
  change -mertensError ≤ (∑ p ∈ T, Real.log p / p) - Real.log x at hx'
  have hbase : Real.log x - Real.log L - 2 * mertensError -
      (∑ p ∈ B, Real.log p / p) ≤ ∑ p ∈ S, Real.log p / p := by
    rw [hS]; linarith [sum_inter_add_sum_sdiff T (B ∪ U) (fun p : ℕ => Real.log p / p)]
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime :=
    (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).1).1).2
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((S.sup id : ℕ) : ℝ) / L) (by norm_num : (1 : ℝ) < 4)
  have htail := prime_sqrt_tail_le_of_pow_bound n hL S hprime (fun _ hp => (mem_filter.mp hp).2)
    fun p hp => (show (p : ℝ) ≤ (S.sup id : ℕ) by exact_mod_cast le_sup (f := id) hp).trans
      ((div_lt_iff₀ (by linarith)).mp hn).le
  have hs : ∑ p ∈ S, (Real.log p / p - C * (Real.log p / p / Real.sqrt p)) ≤
      ∑ p ∈ S, Real.log p / N p := sum_le_sum fun p hp => by
    obtain ⟨hm1, hm2⟩ := mem_filter.mp hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hprime p hp).one_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
    have hrec : 1 / (p : ℝ) - C / (p * Real.sqrt p) ≤ 1 / (p + C * Real.sqrt p) := by
      rw [le_div_iff₀ (by positivity)]
      field_simp
      nlinarith [sq_nonneg C, Real.sq_sqrt hp0.le]
    calc Real.log p / p - C * (Real.log p / p / Real.sqrt p)
        = Real.log p * (1 / p - C / (p * Real.sqrt p)) := by ring
      _ ≤ Real.log p * (1 / (p + C * Real.sqrt p)) := mul_le_mul_of_nonneg_left hrec (Real.log_nonneg hp1)
      _ ≤ Real.log p / N p := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_left (Real.log_nonneg hp1) (hN p hm1 hm2) (hupper p hm1 hm2)
  rw [sum_sub_distrib, ← mul_sum] at hs
  change _ ≤ ∑ p ∈ S, Real.log p / N p
  nlinarith

end
end CCDN
