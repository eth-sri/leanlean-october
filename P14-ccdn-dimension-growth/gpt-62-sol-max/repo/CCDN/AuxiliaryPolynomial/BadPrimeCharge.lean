/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
public import CCDN.AuxiliaryPolynomial.DegreeBound
import CCDN.Analysis.PrimeProduct

/-! Analytic control of bad-prime charges from an integer witness.
The construction and coefficient bound for a Noether witness remain separate. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

private lemma prime_charge_le_of_lower_bound (P : Finset ℕ) {T : ℝ} (hT : 0 < T)
    (hlo : ∀ p ∈ P, T ≤ (p : ℝ)) :
    (∑ p ∈ P, Real.log p / p) ≤ (∑ p ∈ P, Real.log p) / T := by
  rw [sum_div]
  exact sum_le_sum fun p hp => div_le_div_of_nonneg_left (log_natCast_nonneg p) hT (hlo p hp)

section

variable (P : Finset ℕ) {D : ℤ} (hD : 0 < D)
  (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, (p : ℤ) ∣ D)
include P D hD hP hdiv

/-- Distinct prime divisors of a positive integer have total logarithmic
weight at most the logarithm of that integer. -/
lemma prime_divisor_log_sum_le :
    (∑ p ∈ P, Real.log p) ≤ Real.log D := by
  simpa only [Nat.cast_one, one_mul] using sum_log_prime_powers_le_log P (fun _ => 1)
    hD hP (fun p hp => by simp_all)

/-- Above a cutoff T, the reciprocal-weighted charge costs at most log(D)/T. -/
lemma prime_divisor_charge_le
    {T : ℝ} (hT : 0 < T) (hlo : ∀ p ∈ P, T ≤ (p : ℝ)) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log D / T := by
  exact (prime_charge_le_of_lower_bound P hT hlo).trans
    (div_le_div_of_nonneg_right (prime_divisor_log_sum_le P hD hP hdiv) hT.le)

end

/-- Split at `LH`: the primes up to the cutoff have bounded Mertens weight, and the
logarithmic budget bounds the reciprocal charge of the remaining primes. -/
theorem bad_prime_charge_of_log_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {L H : ℝ} (hL : 1 ≤ L) (hH : 1 ≤ H) (hlo : ∀ p ∈ P, L < (p : ℝ))
    (hbudget : (∑ p ∈ P, Real.log p) ≤ L * H) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log H + 2 * mertensError + 1 := by
  classical
  let T := L * H
  let U := P.filter (fun p : ℕ => (p : ℝ) ≤ T)
  let V := P.filter (fun p : ℕ => ¬ (p : ℝ) ≤ T)
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := by linarith
  have hT : 0 < T := mul_pos hL0 hH0
  have hlow := prime_interval_weight_le hL (le_mul_of_one_le_right hL0.le hH) U
    (fun p hp => hP p (mem_filter.mp hp).1)
    (fun p hp => hlo p (mem_filter.mp hp).1)
    (fun _ hp => (mem_filter.mp hp).2)
  have hhigh := (prime_charge_le_of_lower_bound V hT (fun _ hp => (lt_of_not_ge (mem_filter.mp hp).2).le)).trans
    ((div_le_one hT).mpr ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans hbudget))
  rw [Real.log_mul hL0.ne' hH0.ne'] at hlow
  linarith [sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) ≤ T) (fun p : ℕ => Real.log p / p)]

end
end CCDN
