/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.AuxiliaryPolynomial.ScalingPrime
import CCDN.AuxiliaryPolynomial.BadPrimeCharge

/-! A fixed multiplicative prime window has enough product to avoid every
integer of prescribed logarithmic height, and only O(L/log L) primes.
These are the arithmetic inputs to the residue-class cover. -/

@[expose] public section
namespace CCDN
open Finset Real

/-- The primes `p` with `L < p ≤ c L`, where `c` is `scalingPrimeRatio`. -/
noncomputable def congruencePrimeWindow (L : ℝ)  :=
  ((Ioc 0 ⌊scalingPrimeRatio * L⌋₊).filter Nat.Prime) \
    ((Ioc 0 ⌊L⌋₊).filter Nat.Prime)

variable {L : ℝ} (hL : 1 ≤ L)

include hL in
/-- For `L ≥ 1`, a natural number lies in `congruencePrimeWindow L` exactly when it is a prime
`p` with `L < p ≤ c L`, where `c` is `scalingPrimeRatio`. -/
lemma mem_congruencePrimeWindow  {p : ℕ} :
    p ∈ congruencePrimeWindow L ↔
      p.Prime ∧ L < ↑p ∧ ↑p ≤ scalingPrimeRatio * L := by
  have hA := scalingPrimeRatio_one_le
  have hAL : 0 ≤ scalingPrimeRatio * L := by positivity
  constructor
  · intro hp
    obtain ⟨hpV, hpU⟩ := mem_sdiff.mp hp
    have hprime := (mem_filter.mp hpV).2
    refine ⟨hprime, ?_, (prime_mem_upto_iff hAL hprime).mp hpV⟩
    exact lt_of_not_ge (fun h => hpU
      ((prime_mem_upto_iff (by linarith) hprime).mpr h))
  · rintro ⟨hp, hlo, hhi⟩
    exact mem_sdiff.mpr ⟨(prime_mem_upto_iff hAL hp).mpr hhi,
      fun hh => (not_le_of_gt hlo) ((prime_mem_upto_iff (by linarith) hp).mp hh)⟩

include hL in
private lemma congruencePrimeWindow_weight_lower  :
    2 ≤ ∑ p ∈ congruencePrimeWindow L, Real.log p / p := by
  have hA := scalingPrimeRatio_one_le
  have hL0 : 0 < L := by linarith
  have hA0 : 0 < scalingPrimeRatio := by linarith
  have h := prime_interval_weight_lower hL
    (show L ≤ scalingPrimeRatio * L by nlinarith)
  rw [Real.log_mul hA0.ne' hL0.ne'] at h
  have hlogA : Real.log scalingPrimeRatio = 2 * mertensError + 2 := Real.log_exp _
  rw [hlogA] at h
  dsimp only [congruencePrimeWindow]
  linarith

include hL in
private theorem congruencePrimeWindow_log_mass  :
    2 * L ≤ ∑ p ∈ congruencePrimeWindow L, Real.log p := by
  have hL0 : 0 ≤ L := by linarith
  have hm := mul_le_mul_of_nonneg_left (congruencePrimeWindow_weight_lower hL) hL0
  have hterm : L * (∑ p ∈ congruencePrimeWindow L, Real.log p / p) ≤
      ∑ p ∈ congruencePrimeWindow L, Real.log p := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hmem := (mem_congruencePrimeWindow hL).mp hp
    have hp0 : 0 < p := by exact_mod_cast hmem.1.pos
    calc
      _ ≤ ↑p * (Real.log p / p) :=
        mul_le_mul_of_nonneg_right hmem.2.1.le (by positivity)
      _ = _ := by field_simp
  linarith

include hL in
/-- For `L ≥ 1`, the sum of `log p` over the primes of `congruencePrimeWindow L` is at most
`(log 4 + 4) c L`, where `c` is `scalingPrimeRatio`. -/
theorem congruencePrimeWindow_log_upper  :
    (∑ p ∈ congruencePrimeWindow L, Real.log p) ≤
      (Real.log 4 + 4) * scalingPrimeRatio * L := by
  have hA := scalingPrimeRatio_one_le
  have hs : (∑ p ∈ congruencePrimeWindow L, Real.log p) ≤
      Chebyshev.theta (scalingPrimeRatio * L) :=
    sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p _ _ => Real.log_natCast_nonneg p)
  exact hs.trans ((Chebyshev.theta_le_psi _).trans
    (by simpa only [mul_assoc] using
      Chebyshev.psi_le_const_mul_self (show 0 ≤ scalingPrimeRatio * L by positivity)))

include hL in
/-- For `L ≥ 1`, the number of primes in `congruencePrimeWindow L`, multiplied by `log L`, is
at most `(log 4 + 4) c L`, where `c` is `scalingPrimeRatio`. -/
theorem congruencePrimeWindow_card_log_bound  :
    (congruencePrimeWindow L).card * Real.log L ≤
      (Real.log 4 + 4) * scalingPrimeRatio * L := by
  calc
    _ = ∑ _p ∈ congruencePrimeWindow L, Real.log L := by simp
    _ ≤ ∑ p ∈ congruencePrimeWindow L, Real.log p := by
      grind [sum_le_sum, Real.log_le_log, mem_congruencePrimeWindow]
    _ ≤ _ := congruencePrimeWindow_log_upper hL


include hL in
/-- For `L ≥ 1` and a nonzero integer `D` with `log |D| ≤ L`, the product of the primes of
`congruencePrimeWindow L` not dividing `D` is at least `exp L`. -/
theorem congruencePrimeWindow_avoiding_product 
    {D : ℤ} (hD : D ≠ 0) (hheight : Real.log |↑D| ≤ L) :
    Real.exp L ≤
      ∏ p ∈ (congruencePrimeWindow L).filter (fun p : ℕ => ¬ ↑p ∣ D), ↑p := by
  classical
  have hm := (show (2 : ℝ) * L - log |↑D| ≤ ∑ p ∈ congruencePrimeWindow L with ¬↑p ∣ D, log ↑p from (by
               classical
               let bad := (congruencePrimeWindow L).filter (fun p : ℕ => ↑p ∣ D)
               have hbad := by
                 have h := prime_divisor_log_sum_le bad (abs_pos.mpr hD)
                   (fun p hp => ((mem_congruencePrimeWindow hL).mp (mem_filter.mp hp).1).1)
                   (fun p hp => (dvd_abs _ _).mpr (mem_filter.mp hp).2)
                 simpa only [Int.cast_abs] using h
               have hsplit := sum_filter_add_sum_filter_not (congruencePrimeWindow L)
                 (fun p : ℕ => ↑p ∣ D) (fun p : ℕ => Real.log p)
               have htotal := congruencePrimeWindow_log_mass hL
               change (∑ p ∈ bad, Real.log p) + _ = _ at hsplit
               linarith))
  have hlo : L ≤ ∑ p ∈ (congruencePrimeWindow L).filter
      (fun p : ℕ => ¬ ↑p ∣ D), Real.log p := by linarith
  have hp (p : ℕ) (hp : p ∈ (congruencePrimeWindow L).filter
      (fun p : ℕ => ¬ ↑p ∣ D)) : (0 : ℝ) < p := by
    grind [mem_congruencePrimeWindow]
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')] at hlo
  exact (Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log (prod_pos hp))

end CCDN
