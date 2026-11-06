/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import CCDN.Analysis.PrimeCutoff
import CCDN.AuxiliaryPolynomial.BadPrimeCharge

/-! A scaling prime from the first Mertens estimate. If every prime in a fixed
multiplicative interval divides a nonzero integer, that integer has large
logarithmic height. -/

@[expose] public section
namespace CCDN
open Finset Real

variable {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T)

include hL hLT in
/-- Lower bound from the first Mertens estimate: for `1 ≤ L ≤ T`, the sum of `log p / p` over the
primes `p` with `L < p ≤ T` is at least `log T - log L - 2 mertensError`. -/
lemma prime_interval_weight_lower  :
    Real.log T - Real.log L - 2 * mertensError ≤
      ∑ p ∈ ((Ioc 0 ⌊T⌋₊).filter Nat.Prime) \ ((Ioc 0 ⌊L⌋₊).filter Nat.Prime),
        Real.log p / p := by
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  let V := (Ioc 0 ⌊T⌋₊).filter Nat.Prime
  have hUV : U ⊆ V := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    exact (prime_mem_upto_iff (by linarith) hp').mpr
      (((prime_mem_upto_iff (by linarith) hp').mp hp).trans hLT)
  have hsplit := sum_sdiff hUV (f := fun p : ℕ => Real.log p / p)
  have hl := (abs_le.mp (Mertens.prime_sum_bounded_error hL)).2
  have ht := (abs_le.mp (Mertens.prime_sum_bounded_error (hL.trans hLT))).1
  change (∑ p ∈ U, Real.log p / p) - Real.log L ≤ mertensError at hl
  change -mertensError ≤ (∑ p ∈ V, Real.log p / p) - Real.log T at ht
  change _ ≤ ∑ p ∈ V \ U, Real.log p / p
  linarith

include hL hLT in
private theorem exists_prime_interval_not_dvd 
    {D : ℤ} (hD : 0 < D)
    (hheight : Real.log D / L < Real.log T - Real.log L - 2 * mertensError) :
    ∃ p : ℕ, p.Prime ∧ L < p ∧ ↑p ≤ T ∧ ¬ ↑p ∣ D := by
  classical
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  let V := (Ioc 0 ⌊T⌋₊).filter Nat.Prime
  have hmem (p : ℕ) (hp : p ∈ V \ U) : p.Prime ∧ L < p ∧ ↑p ≤ T := by
    grind [prime_mem_upto_iff]
  by_contra hnone
  have hdiv : ∀ p ∈ V \ U, ↑p ∣ D := by
    simp_all
  have hupper := prime_divisor_charge_le (V \ U) hD (fun p hp => (hmem p hp).1) hdiv
    (show 0 < L by linarith) (fun p hp => (hmem p hp).2.1.le)
  have hlower := prime_interval_weight_lower hL hLT
  exact (not_lt_of_ge (hlower.trans hupper)) hheight

/-- The absolute constant `A = exp (2 mertensError + 2)` such that a prime in the interval
`(B / A, B]` can be found avoiding the prime divisors of any nonzero integer `D` with
`log |D| < B / A`. -/
noncomputable def scalingPrimeRatio  := Real.exp (2 * mertensError + 2)

/-- The scaling-prime ratio is at least one. -/
lemma scalingPrimeRatio_one_le : 1 ≤ scalingPrimeRatio := by
  unfold scalingPrimeRatio
  apply Real.one_le_exp_iff.mpr
  have := mertensError_pos
  linarith

/-- A prime of size comparable to B avoids D when log |D| < B/A, where
A=exp(2*mertensError+2) is an absolute constant. -/
theorem exists_scaling_prime {B : ℝ} (hB : scalingPrimeRatio ≤ B)
    {D : ℤ} (hD : D ≠ 0) (hheight : Real.log |↑D| < B / scalingPrimeRatio) :
    ∃ p : ℕ, p.Prime ∧ B / scalingPrimeRatio < p ∧ ↑p ≤ B ∧ ¬ ↑p ∣ D := by
  have hA := scalingPrimeRatio_one_le
  have hA0 : 0 < scalingPrimeRatio := by linarith
  have hB0 : 0 < B := by linarith
  have hL : 1 ≤ B / scalingPrimeRatio := (le_div_iff₀ hA0).mpr (by linarith)
  have hLB : B / scalingPrimeRatio ≤ B := by
    simp_all [div_le_iff₀]
  have hwidth : Real.log B - Real.log (B / scalingPrimeRatio) - 2 * mertensError = 2 := by
    rw [Real.log_div hB0.ne' hA0.ne']
    simp only [scalingPrimeRatio, Real.log_exp]
    ring
  have hheight' : Real.log (|D| : ℤ) / (B / scalingPrimeRatio) <
      Real.log B - Real.log (B / scalingPrimeRatio) - 2 * mertensError := by
    have he : ((|D| : ℤ) : ℝ) = |↑D| := by norm_cast
    rw [he]
    have hh :=
      (div_lt_one (by positivity)).mpr hheight
    linarith
  obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_prime_interval_not_dvd hL hLB (abs_pos.mpr hD) hheight'
  refine ⟨p, hp, hlo, hhi, ?_⟩
  intro hdiv
  exact hnd ((dvd_abs _ _).mpr hdiv)

end CCDN
