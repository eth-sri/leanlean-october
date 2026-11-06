/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.ScalingPrime
import CCDN.AuxiliaryPolynomial.BadPrimeCharge

/-! A fixed multiplicative prime window has enough product to avoid every
integer of prescribed logarithmic height, and only O(L/log L) primes.
These are the arithmetic inputs to the residue-class cover. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

/-- The primes `p` with `L < p ≤ c L`, where `c` is `scalingPrimeRatio`. -/
def congruencePrimeWindow (L : ℝ) : Finset ℕ :=
  ((Ioc 0 ⌊scalingPrimeRatio * L⌋₊).filter Nat.Prime) \
    ((Ioc 0 ⌊L⌋₊).filter Nat.Prime)

/-- For `L ≥ 1`, a natural number lies in `congruencePrimeWindow L` exactly when it is a prime
`p` with `L < p ≤ c L`, where `c` is `scalingPrimeRatio`. -/
lemma mem_congruencePrimeWindow {L : ℝ} (hL : 1 ≤ L) {p : ℕ} :
    p ∈ congruencePrimeWindow L ↔
      p.Prime ∧ L < (p : ℝ) ∧ (p : ℝ) ≤ scalingPrimeRatio * L := by
  have hA := scalingPrimeRatio_one_le
  have hAL : 0 ≤ scalingPrimeRatio * L := by positivity
  constructor
  · intro hp
    obtain ⟨hpV, hpU⟩ := mem_sdiff.mp hp
    have hprime := (mem_filter.mp hpV).2
    exact ⟨hprime, lt_of_not_ge fun h => hpU
      ((prime_mem_upto_iff (by linarith) hprime).mpr h),
      (prime_mem_upto_iff hAL hprime).mp hpV⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact mem_sdiff.mpr ⟨(prime_mem_upto_iff hAL hp).mpr hhi,
      fun hh => (not_le_of_gt hlo) ((prime_mem_upto_iff (by linarith) hp).mp hh)⟩

/-- For `L ≥ 1`, the sum of `log p` over the primes of `congruencePrimeWindow L` is at most
`(log 4 + 4) c L`, where `c` is `scalingPrimeRatio`. -/
theorem congruencePrimeWindow_log_upper {L : ℝ} (hL : 1 ≤ L) :
    (∑ p ∈ congruencePrimeWindow L, Real.log p) ≤
      (Real.log 4 + 4) * scalingPrimeRatio * L := by
  have hA := scalingPrimeRatio_one_le
  exact (sum_le_sum_of_subset_of_nonneg sdiff_subset fun p _ _ =>
    Real.log_natCast_nonneg p).trans ((Chebyshev.theta_le_psi _).trans
      (by simpa only [mul_assoc] using
        Chebyshev.psi_le_const_mul_self (show 0 ≤ scalingPrimeRatio * L by positivity)))

/-- For `L ≥ 1`, the number of primes in `congruencePrimeWindow L`, multiplied by `log L`, is
at most `(log 4 + 4) c L`, where `c` is `scalingPrimeRatio`. -/
theorem congruencePrimeWindow_card_log_bound {L : ℝ} (hL : 1 ≤ L) :
    (congruencePrimeWindow L).card * Real.log L ≤
      (Real.log 4 + 4) * scalingPrimeRatio * L := by
  calc (congruencePrimeWindow L).card * Real.log L
    _ = ∑ _p ∈ congruencePrimeWindow L, Real.log L := by simp
    _ ≤ ∑ p ∈ congruencePrimeWindow L, Real.log p := sum_le_sum fun p hp =>
      Real.log_le_log (by linarith) ((mem_congruencePrimeWindow hL).mp hp).2.1.le
    _ ≤ _ := congruencePrimeWindow_log_upper hL

/-- For `L ≥ 1` and a nonzero integer `D` with `log |D| ≤ L`, the product of the primes of
`congruencePrimeWindow L` not dividing `D` is at least `exp L`. -/
theorem congruencePrimeWindow_avoiding_product {L : ℝ} (hL : 1 ≤ L)
    {D : ℤ} (hD : D ≠ 0) (hheight : Real.log |(D : ℝ)| ≤ L) :
    Real.exp L ≤
      ∏ p ∈ (congruencePrimeWindow L).filter (fun p : ℕ => ¬ (p : ℤ) ∣ D), (p : ℝ) := by
  classical
  have hA := scalingPrimeRatio_one_le
  have hL0 : 0 < L := by linarith
  have hA0 : 0 < scalingPrimeRatio := by linarith
  have h := prime_interval_weight_lower hL (show L ≤ scalingPrimeRatio * L by nlinarith)
  rw [Real.log_mul hA0.ne' hL0.ne', show Real.log scalingPrimeRatio = 2 * mertensError + 2 from
    Real.log_exp _] at h
  have hm := mul_le_mul_of_nonneg_left (show 2 ≤ ∑ p ∈ congruencePrimeWindow L, Real.log p / p by
    dsimp [congruencePrimeWindow]; linarith) hL0.le
  have hterm : L * (∑ p ∈ congruencePrimeWindow L, Real.log p / p) ≤
      ∑ p ∈ congruencePrimeWindow L, Real.log p := by
    rw [mul_sum]
    refine sum_le_sum fun p hp => ?_
    have hmem := (mem_congruencePrimeWindow hL).mp hp
    have hp0 : (0 : ℝ) < p := mod_cast hmem.1.pos
    exact (mul_le_mul_of_nonneg_right hmem.2.1.le (by positivity)).trans_eq (by field_simp)
  let bad := (congruencePrimeWindow L).filter fun p : ℕ => (p : ℤ) ∣ D
  have hbad : (∑ p ∈ bad, Real.log p) ≤ Real.log |(D : ℝ)| := by
    simpa only [Int.cast_abs] using prime_divisor_log_sum_le bad (abs_pos.mpr hD)
      (fun p hp => ((mem_congruencePrimeWindow hL).mp (mem_filter.mp hp).1).1)
      (fun p hp => (dvd_abs _ _).mpr (mem_filter.mp hp).2)
  have hsplit := sum_filter_add_sum_filter_not (congruencePrimeWindow L)
    (fun p : ℕ => (p : ℤ) ∣ D) (fun p : ℕ => Real.log p)
  have hlo : L ≤ ∑ p ∈ (congruencePrimeWindow L).filter
      (fun p : ℕ => ¬ (p : ℤ) ∣ D), Real.log p := by linarith
  have hp (p : ℕ) (hp : p ∈ (congruencePrimeWindow L).filter
      (fun p : ℕ => ¬ (p : ℤ) ∣ D)) : (0 : ℝ) < p :=
    mod_cast ((mem_congruencePrimeWindow hL).mp (mem_filter.mp hp).1).1.pos
  rw [← Real.log_prod fun p hp' => (hp p hp').ne'] at hlo
  exact (Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log (prod_pos hp))

end
end CCDN
