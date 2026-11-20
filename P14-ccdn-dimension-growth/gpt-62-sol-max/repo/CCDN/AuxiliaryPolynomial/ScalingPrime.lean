/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
import CCDN.AuxiliaryPolynomial.BadPrimeCharge

/-! A scaling prime from the first Mertens estimate. If every prime in a fixed
multiplicative interval divides a nonzero integer, that integer has large
logarithmic height. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

section

variable {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T)
include L T hL hLT

private theorem exists_prime_interval_not_dvd
    {D : ℤ} (hD : 0 < D)
    (hheight : Real.log D / L < Real.log T - Real.log L - 2 * mertensError) :
    ∃ p : ℕ, p.Prime ∧ L < p ∧ (p : ℝ) ≤ T ∧ ¬ (p : ℤ) ∣ D := by
  by_contra hnone
  have hdvd (p) (hp : p ∈ primesInInterval L T) : (p : ℤ) ∣ D := by
    obtain ⟨hP, hlo, hhi⟩ := mem_primesInInterval.mp hp
    grind
  have hupper := prime_divisor_charge_le (primesInInterval L T) hD (fun p hp => (mem_primesInInterval.mp hp).1) hdvd
    (show 0 < L by linarith) (fun p hp => (mem_primesInInterval.mp hp).2.1.le)
  linarith [(prime_interval_weight_bounds hL hLT).1]

end

/-- The absolute constant `A = exp (2 mertensError + 2)` such that a prime in the interval
`(B / A, B]` can be found avoiding the prime divisors of any nonzero integer `D` with
`log |D| < B / A`. -/
def scalingPrimeRatio : ℝ := Real.exp (2 * mertensError + 2)

/-- The scaling-prime ratio is at least one. -/
lemma scalingPrimeRatio_one_le : 1 ≤ scalingPrimeRatio := by
  unfold scalingPrimeRatio
  apply Real.one_le_exp_iff.mpr
  have := mertensError_pos
  linarith

/-- A prime of size comparable to B avoids D when log |D| < B/A, where
A=exp(2*mertensError+2) is an absolute constant. -/
theorem exists_scaling_prime {B : ℝ} (hB : scalingPrimeRatio ≤ B)
    {D : ℤ} (hD : D ≠ 0) (hheight : Real.log |(D : ℝ)| < B / scalingPrimeRatio) :
    ∃ p : ℕ, p.Prime ∧ B / scalingPrimeRatio < p ∧ (p : ℝ) ≤ B ∧ ¬ (p : ℤ) ∣ D := by
  have hA := scalingPrimeRatio_one_le
  have hA0 : 0 < scalingPrimeRatio := by linarith
  have hB0 : 0 < B := by linarith
  have hL : 1 ≤ B / scalingPrimeRatio := (le_div_iff₀ hA0).mpr (by linarith)
  have hLB : B / scalingPrimeRatio ≤ B := by
    apply (div_le_iff₀ hA0).mpr
    nlinarith
  have hwidth : Real.log B - Real.log (B / scalingPrimeRatio) - 2 * mertensError = 2 := by
    rw [Real.log_div hB0.ne' hA0.ne']
    simp [scalingPrimeRatio]
  have hheight' : Real.log (|D| : ℤ) / (B / scalingPrimeRatio) <
      Real.log B - Real.log (B / scalingPrimeRatio) - 2 * mertensError := by
    rw [Int.cast_abs, hwidth]
    linarith [(div_lt_one (by positivity : 0 < B / scalingPrimeRatio)).mpr hheight]
  obtain ⟨p, hp, hlo, hhi, hnd⟩ := exists_prime_interval_not_dvd hL hLB (abs_pos.mpr hD) hheight'
  refine ⟨p, hp, hlo, hhi, ?_⟩; aesop

end
end CCDN
