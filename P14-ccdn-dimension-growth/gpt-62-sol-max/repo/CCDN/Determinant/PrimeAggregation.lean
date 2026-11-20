/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
public import CCDN.Plane.FiniteFieldConstants
import CCDN.Analysis.PrimeProduct

/-! Combine the good-prime and prescribed-prime determinant divisors. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

private lemma sum_log_disjoint_prime_powers_le_log (P Q : Finset ℕ)
    (hPQ : Disjoint P Q) (e v : ℕ → ℕ) {D : ℤ} (hD : 0 < D)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ Q, p.Prime)
    (hdivP : ∀ p ∈ P, (p : ℤ) ^ e p ∣ D)
    (hdivQ : ∀ p ∈ Q, (p : ℤ) ^ v p ∣ D) :
    (∑ p ∈ P, (e p : ℝ) * Real.log p) +
      (∑ p ∈ Q, (v p : ℝ) * Real.log p) ≤ Real.log D := by
  classical
  let w := fun p => if p ∈ P then e p else v p
  have hw (p : ℕ) (hp : p ∈ P ∪ Q) : (p : ℤ) ^ w p ∣ D := by
    by_cases h : p ∈ P <;> aesop
  have hh := sum_log_prime_powers_le_log (P ∪ Q) w hD
    (fun p hp => (mem_union.mp hp).elim (hP p) (hQ p)) hw
  rw [sum_union hPQ] at hh
  have h₁ : (∑ p ∈ P, (w p : ℝ) * Real.log p) =
      ∑ p ∈ P, (e p : ℝ) * Real.log p := by
    aesop
  have h₂ : (∑ p ∈ Q, (w p : ℝ) * Real.log p) =
      ∑ p ∈ Q, (v p : ℝ) * Real.log p := by
    apply sum_congr rfl
    intro p hp
    have hn : p ∉ P := fun h => (disjoint_left.mp hPQ) h hp
    aesop
  linarith

/-- Good primes used in the determinant bound: above the Stepanov cutoff,
up to `x`, and outside the excluded set. -/
noncomputable def determinantPrimes (x : ℝ) (d : ℕ) (bad : Finset ℕ) : Finset ℕ :=
  primesInInterval (stepanovThreshold d) x \ bad

lemma mem_determinantPrimes {x : ℝ} {d p : ℕ} {bad : Finset ℕ}
    (hp : p ∈ determinantPrimes x d bad) :
    p.Prime ∧ p ∉ bad ∧ stepanovThreshold (d : ℝ) < p := by
  obtain ⟨hp, hn⟩ := mem_sdiff.mp hp
  obtain ⟨hp, hlo, _⟩ := mem_primesInInterval.mp hp
  exact ⟨hp, hn, hlo⟩

/-- Aggregate the local determinant divisors. The assigned primes `P` are
excluded from the good-prime sum and each contributes its full exponent `v`. -/
theorem determinant_log_lower_of_local_divisors {x K A E : ℝ} {d : ℕ}
    (hx : 1 ≤ x) (hd : 0 < d) (hK : 0 ≤ K) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (bad P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (v : ℕ) {D : ℤ} (hD : 0 < D)
    (hlocal : ∀ p ∈ determinantPrimes x d (bad ∪ P),
      ∃ e : ℕ, A / (p + K * (d : ℝ) ^ 2 * Real.sqrt p) - E ≤ e ∧ (p : ℤ) ^ e ∣ D)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v ∣ D) :
    A * (Real.log x - 4 * Real.log d - Real.log 27 - 2 * mertensError -
      (∑ p ∈ bad ∪ P, Real.log p / p) - 2 * K * primeBlockMass) -
      E * ((Real.log 4 + 4) * x) + (v : ℝ) * (∑ p ∈ P, Real.log p) ≤ Real.log D := by
  classical
  let L := stepanovThreshold (d : ℝ)
  let C := K * (d : ℝ) ^ 2
  let N (p : ℕ) := (p : ℝ) + C * Real.sqrt p
  let S := determinantPrimes x d (bad ∪ P)
  have hSP : Disjoint S P := disjoint_left.mpr fun p hp hp' =>
    (mem_determinantPrimes hp).2.1 (mem_union_right bad hp')
  let e (p : ℕ) := if hp : p ∈ S then (hlocal p hp).choose else 0
  have he (p : ℕ) (hp : p ∈ S) : A / N p - E ≤ e p ∧ (p : ℤ) ^ e p ∣ D := by
    simpa [e, hp] using (hlocal p hp).choose_spec
  have hsum := sum_log_disjoint_prime_powers_le_log S P hSP e (fun _ => v) hD
    (fun _ hp => (mem_determinantPrimes hp).1) hP (fun p hp => (he p hp).2) hcong
  rw [← mul_sum] at hsum
  have hbound : A * (∑ p ∈ S, Real.log p / N p) - E * (∑ p ∈ S, Real.log p) ≤
      ∑ p ∈ S, (e p : ℝ) * Real.log p := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_le_sum
    intro p hp
    convert mul_le_mul_of_nonneg_right (he p hp).1 (Real.log_natCast_nonneg p) using 1
    ring
  have htheta := (sum_le_sum_of_subset_of_nonneg (s := S)
    (sdiff_subset.trans sdiff_subset) (fun p _ _ => Real.log_natCast_nonneg p)).trans
      ((Chebyshev.theta_le_psi x).trans (Chebyshev.psi_le_const_mul_self (by linarith)))
  have hL : 1 ≤ L := 
    (one_le_pow₀ (n := 4) (by exact_mod_cast hd)).trans (le_mul_of_one_le_left (by positivity) (by norm_num))
  have hLlog : Real.log L = Real.log 27 + 4 * Real.log d := by
    rw [show L = 27 * (d : ℝ) ^ 4 by rfl, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hm := weighted_prime_sum_lower_cutoff hx hL (show 0 ≤ C by positivity) (bad ∪ P)
  change _ ≤ ∑ p ∈ S, Real.log p / N p at hm
  have hsqrt : (d : ℝ) ^ 2 ≤ Real.sqrt L := by
    apply Real.le_sqrt_of_sq_le
    dsimp [L, stepanovThreshold]
    nlinarith
  have htail : C * (2 * primeBlockMass / Real.sqrt L) ≤ 2 * K * primeBlockMass := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))).mpr
    have h := mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (by positivity : 0 ≤ 2 * K) primeBlockMass_pos.le)
    dsimp [C]
    nlinarith
  rw [hLlog] at hm
  linarith only [hsum, hbound, mul_le_mul_of_nonneg_left hm hA,
    mul_le_mul_of_nonneg_left htail hA, mul_le_mul_of_nonneg_left htheta hE]

end
end CCDN
