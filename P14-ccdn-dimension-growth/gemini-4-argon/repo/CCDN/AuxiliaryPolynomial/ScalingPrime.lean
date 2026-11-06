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

/-- The absolute constant `A = exp (2 mertensError + 2)` such that a prime in the interval
`(B / A, B]` can be found avoiding the prime divisors of any nonzero integer `D` with
`log |D| < B / A`. -/
def scalingPrimeRatio : ℝ := Real.exp (2 * mertensError + 2)

/-- The scaling-prime ratio is at least one. -/
lemma scalingPrimeRatio_one_le : 1 ≤ scalingPrimeRatio :=
  Real.one_le_exp_iff.mpr (by linarith [mertensError_pos])

/-- A prime of size comparable to B avoids D when log |D| < B/A, where
A=exp(2*mertensError+2) is an absolute constant. -/
theorem exists_scaling_prime {B : ℝ} (hB : scalingPrimeRatio ≤ B)
    {D : ℤ} (hD : D ≠ 0) (hheight : Real.log |(D : ℝ)| < B / scalingPrimeRatio) :
    ∃ p : ℕ, p.Prime ∧ B / scalingPrimeRatio < p ∧ (p : ℝ) ≤ B ∧ ¬ (p : ℤ) ∣ D := by
  classical
  have hA := scalingPrimeRatio_one_le
  have hA0 : 0 < scalingPrimeRatio := by linarith
  have hB0 : 0 < B := by linarith
  let L := B / scalingPrimeRatio
  have hL : 1 ≤ L := (le_div_iff₀ hA0).mpr (by linarith)
  have hLB : L ≤ B := (div_le_iff₀ hA0).mpr (by nlinarith)
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  let V := (Ioc 0 ⌊B⌋₊).filter Nat.Prime
  have hmem (p : ℕ) (hp : p ∈ V \ U) : p.Prime ∧ L < p ∧ (p : ℝ) ≤ B := by
    have hpV := (mem_sdiff.mp hp).1
    have hpP := (mem_filter.mp hpV).2
    refine ⟨hpP, lt_of_not_ge fun hle => (mem_sdiff.mp hp).2
      ((prime_mem_upto_iff (by linarith) hpP).mpr hle),
      (prime_mem_upto_iff (by linarith) hpP).mp hpV⟩
  by_contra! hnone
  have hdiv : ∀ p ∈ V \ U, (p : ℤ) ∣ |D| := fun p hp =>
    (dvd_abs _ _).mpr (hnone p (hmem p hp).1 (hmem p hp).2.1 (hmem p hp).2.2)
  have hupper := prime_divisor_charge_le (V \ U) (abs_pos.mpr hD) (fun p hp => (hmem p hp).1) hdiv
    (by linarith : 0 < L) (fun p hp => (hmem p hp).2.1.le)
  have hlower := prime_interval_weight_lower hL hLB
  have hwidth : Real.log B - Real.log L - 2 * mertensError = 2 := by
    rw [Real.log_div hB0.ne' hA0.ne']
    simp only [scalingPrimeRatio, Real.log_exp]; ring
  have hh : Real.log ((|D| : ℤ) : ℝ) / L < 1 := by
    rw [Int.cast_abs]; exact (div_lt_one (by linarith)).mpr hheight
  linarith

end
end CCDN
