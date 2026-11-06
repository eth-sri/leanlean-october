/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
import CCDN.Analysis.PrimeProduct

/-! Analytic control of bad-prime charges from an integer witness.
The construction and coefficient bound for a Noether witness remain separate. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

/-- Distinct prime divisors of a positive integer have total logarithmic
weight at most the logarithm of that integer. -/
lemma prime_divisor_log_sum_le (P : Finset ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, (p : ℤ) ∣ D) :
    (∑ p ∈ P, Real.log p) ≤ Real.log D := by
  simpa only [Nat.cast_one, one_mul] using sum_log_prime_powers_le_log P (fun _ => 1)
    hD hP (fun p hp => by simpa only [pow_one] using hdiv p hp)

/-- Above a cutoff T, the reciprocal-weighted charge costs at most log(D)/T. -/
lemma prime_divisor_charge_le (P : Finset ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, (p : ℤ) ∣ D)
    {T : ℝ} (hT : 0 < T) (hlo : ∀ p ∈ P, T ≤ (p : ℝ)) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log D / T := by
  calc ∑ p ∈ P, Real.log p / p
    _ ≤ ∑ p ∈ P, Real.log p / T :=
      sum_le_sum fun p hp => div_le_div_of_nonneg_left (by positivity) hT (hlo p hp)
    _ = (∑ p ∈ P, Real.log p) / T := (sum_div _ _ _).symm
    _ ≤ Real.log D / T := div_le_div_of_nonneg_right (prime_divisor_log_sum_le P hD hP hdiv) hT.le

/-- A logarithmic-height bound for an integer witness controls the bad-prime
charge at the scale of the cutoff. Constructing such a witness is algebraic. -/
theorem bad_prime_charge_of_height (P : Finset ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, (p : ℤ) ∣ D)
    {L H : ℝ} (hL : 1 ≤ L) (hH : 1 ≤ H) (hlo : ∀ p ∈ P, L < (p : ℝ))
    (hheight : Real.log D ≤ L * H) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log H + 2 * mertensError + 1 := by
  classical
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := by linarith
  let T := L * H
  have hLT : L ≤ T := le_mul_of_one_le_right hL0.le hH
  have hlow := prime_interval_weight_le hL hLT (P.filter fun p : ℕ => (p : ℝ) ≤ T)
    (fun p hp => hP p (mem_filter.mp hp).1)
    (fun p hp => hlo p (mem_filter.mp hp).1) (fun _ hp => (mem_filter.mp hp).2)
  have hhigh := prime_divisor_charge_le (P.filter fun p : ℕ => ¬ (p : ℝ) ≤ T) hD
    (fun p hp => hP p (mem_filter.mp hp).1)
    (fun p hp => hdiv p (mem_filter.mp hp).1) (mul_pos hL0 hH0)
    (fun _ hp => (lt_of_not_ge (mem_filter.mp hp).2).le)
  have hsplit := sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) ≤ T)
    (fun p : ℕ => Real.log p / p)
  have ht : Real.log D / T ≤ 1 := (div_le_one (mul_pos hL0 hH0)).mpr hheight
  rw [show T = L * H from rfl, Real.log_mul hL0.ne' hH0.ne'] at hlow
  linarith

end
end CCDN
