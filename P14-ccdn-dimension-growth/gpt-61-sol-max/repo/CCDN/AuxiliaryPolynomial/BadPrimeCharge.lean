/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Analysis.PrimeCutoff
public import CCDN.AuxiliaryPolynomial.DegreeBound
import CCDN.Analysis.PrimeProduct

/-! Analytic control of bad-prime charges from an integer witness.
The construction and coefficient bound for a Noether witness remain separate. -/

public section
namespace CCDN
open Finset Real

variable (P : Finset ℕ) {D : ℤ} (hD : 0 < D) (hP : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, ↑p ∣ D)

include hD hP hdiv in
/-- Distinct prime divisors of a positive integer have total logarithmic
weight at most the logarithm of that integer. -/
lemma prime_divisor_log_sum_le  :
    (∑ p ∈ P, Real.log p) ≤ Real.log D := by
  simpa only [Nat.cast_one, one_mul] using sum_log_prime_powers_le_log P (fun _ => 1)
    hD hP (fun p hp => by simp_all)

include hD hP hdiv in
/-- Above a cutoff T, the reciprocal-weighted charge costs at most log(D)/T. -/
lemma prime_divisor_charge_le 
    {T : ℝ} (hT : 0 < T) (hlo : ∀ p ∈ P, T ≤ ↑p) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log D / T := by
  calc
    _ ≤ ∑ p ∈ P, Real.log p / T := by
      gcongr ; aesop
    _ = (∑ p ∈ P, Real.log p) / T := (sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (prime_divisor_log_sum_le P hD hP hdiv) hT.le


include hD hP hdiv in
/-- A logarithmic-height bound for an integer witness controls the bad-prime
charge at the scale of the cutoff. Constructing such a witness is algebraic. -/
theorem bad_prime_charge_of_height 
    {L H : ℝ} (hL : 1 ≤ L) (hH : 1 ≤ H) (hlo : ∀ p ∈ P, L < ↑p)
    (hheight : Real.log D ≤ L * H) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log H + 2 * mertensError + 1 := by
  have hL0 : 0 < L := by linarith
  have hH0 : 0 < H := by linarith
  have hLT := le_mul_of_one_le_right hL0.le hH
  have h := (show ∑ p ∈ P, log ↑p / ↑p ≤ log (L * H) - log L + (2 : ℝ) * mertensError + log ↑D / (L * H) from (by
              let inline_T := L * H
              classical
              let U := P.filter (fun p : ℕ => ↑p ≤ inline_T)
              let V := P.filter (fun p : ℕ => ¬ ↑p ≤ inline_T)
              have hlow := (show ∑ p ∈ U, log ↑p / ↑p ≤ log (L * H) - log L + (2 : ℝ) * mertensError from (by
                             let inline_T := L * H
                             let inline_P := U
                             let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
                             let V := (Ioc 0 ⌊inline_T⌋₊).filter Nat.Prime
                             have hUV : U ⊆ V := by
                               intro p hp
                               have hp' := (mem_filter.mp hp).2
                               exact (prime_mem_upto_iff (by linarith) hp').mpr
                                 (((prime_mem_upto_iff (by linarith) hp').mp hp).trans hLT)
                             have hPV : inline_P ⊆ V \ U := by
                               grind [prime_mem_upto_iff]
                             have hsum : (∑ p ∈ inline_P, Real.log p / p) ≤ ∑ p ∈ V \ U, Real.log p / p :=
                               sum_le_sum_of_subset_of_nonneg hPV (fun _ _ _ => by positivity)
                             have hsplit := sum_sdiff hUV (f := fun p : ℕ => Real.log p / p)
                             have hl := (abs_le.mp (Mertens.prime_sum_bounded_error hL)).1
                             have ht := (abs_le.mp (Mertens.prime_sum_bounded_error (hL.trans hLT))).2
                             change -mertensError ≤ (∑ p ∈ U, Real.log p / p) - Real.log L at hl
                             change (∑ p ∈ V, Real.log p / p) - Real.log inline_T ≤ mertensError at ht
                             linarith))
              have hhigh := prime_divisor_charge_le V hD
                (fun p hp => hP p (mem_filter.mp hp).1)
                (fun p hp => hdiv p (mem_filter.mp hp).1)
                (by linarith : 0 < inline_T)
                (fun _ hp => (lt_of_not_ge (mem_filter.mp hp).2).le)
              have hsplit := sum_filter_add_sum_filter_not P (fun p : ℕ => ↑p ≤ inline_T)
                (fun p : ℕ => Real.log p / p)
              change (∑ p ∈ U, Real.log p / p) + (∑ p ∈ V, Real.log p / p) = _ at hsplit
              linarith))
  have ht := (div_le_one (mul_pos hL0 hH0)).mpr hheight
  rw [Real.log_mul hL0.ne' hH0.ne'] at h
  linarith

end CCDN
