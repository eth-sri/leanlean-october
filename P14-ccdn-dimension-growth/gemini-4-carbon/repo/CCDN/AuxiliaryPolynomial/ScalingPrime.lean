/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
import CCDN.AuxiliaryPolynomial.BadPrimeCharge

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

lemma prime_interval_weight_lower {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T) :
    Real.log T - Real.log L - 2 * mertensError ≤
      ∑ p ∈ ((Ioc 0 ⌊T⌋₊).filter Nat.Prime) \ ((Ioc 0 ⌊L⌋₊).filter Nat.Prime),
        Real.log p / p := by
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  let V := (Ioc 0 ⌊T⌋₊).filter Nat.Prime
  have hUV : U ⊆ V := fun p hp => (prime_mem_upto_iff (by linarith) (mem_filter.mp hp).2).mpr
    (((prime_mem_upto_iff (by linarith) (mem_filter.mp hp).2).mp hp).trans hLT)
  have hsplit := sum_sdiff hUV (f := fun p : ℕ => Real.log p / p)
  have hl := (abs_le.mp (Mertens.prime_sum_bounded_error hL)).2
  have ht := (abs_le.mp (Mertens.prime_sum_bounded_error (hL.trans hLT))).1
  change (∑ p ∈ U, Real.log p / p) - Real.log L ≤ mertensError at hl
  change -mertensError ≤ (∑ p ∈ V, Real.log p / p) - Real.log T at ht
  change _ ≤ ∑ p ∈ V \ U, Real.log p / p
  linarith

def scalingPrimeRatio : ℝ := Real.exp (2 * mertensError + 2)

lemma scalingPrimeRatio_one_le : 1 ≤ scalingPrimeRatio :=
  Real.one_le_exp_iff.mpr (by linarith [mertensError_pos])

theorem exists_scaling_prime {B : ℝ} (hB : scalingPrimeRatio ≤ B)
    {D : ℤ} (hD : D ≠ 0) (hheight : Real.log |(D : ℝ)| < B / scalingPrimeRatio) :
    ∃ p : ℕ, p.Prime ∧ B / scalingPrimeRatio < p ∧ (p : ℝ) ≤ B ∧ ¬ (p : ℤ) ∣ D := by
  classical
  have hA := scalingPrimeRatio_one_le
  have hA0 : 0 < scalingPrimeRatio := by linarith
  set L := B / scalingPrimeRatio
  have hL : 1 ≤ L := (le_div_iff₀ hA0).mpr (by linarith)
  have hLB : L ≤ B := div_le_self (by linarith) hA
  let W := ((Ioc 0 ⌊B⌋₊).filter Nat.Prime) \ ((Ioc 0 ⌊L⌋₊).filter Nat.Prime)
  have hmem (p : ℕ) (hp : p ∈ W) : p.Prime ∧ L < p ∧ (p : ℝ) ≤ B := by
    obtain ⟨hpV, hpU⟩ := mem_sdiff.mp hp
    have hpP := (mem_filter.mp hpV).2
    exact ⟨hpP, lt_of_not_ge fun hle => hpU ((prime_mem_upto_iff (by linarith) hpP).mpr hle),
      (prime_mem_upto_iff (by linarith) hpP).mp hpV⟩
  by_contra hnone
  have hupper := prime_divisor_charge_le W (abs_pos.mpr hD) (fun p hp => (hmem p hp).1)
    (fun p hp => (dvd_abs _ _).mpr <| by
      by_contra hnd; exact hnone ⟨p, (hmem p hp).1, (hmem p hp).2.1, (hmem p hp).2.2, hnd⟩)
    (by linarith : 0 < L) (fun p hp => (hmem p hp).2.1.le)
  have hlower := prime_interval_weight_lower hL hLB
  rw [show ((|D| : ℤ) : ℝ) = |(D : ℝ)| by norm_cast] at hupper
  have hwidth : Real.log B - Real.log L - 2 * mertensError = 2 := by
    rw [Real.log_div (by linarith) hA0.ne', scalingPrimeRatio, Real.log_exp]; ring
  have hh : Real.log |(D : ℝ)| / L < 1 := (div_lt_one (by linarith)).mpr hheight
  linarith

end
end CCDN
