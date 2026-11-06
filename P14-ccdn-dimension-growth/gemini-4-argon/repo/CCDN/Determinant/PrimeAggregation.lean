/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Analysis.PrimeCutoff
public import CCDN.Plane.FiniteFieldConstants
import CCDN.Analysis.PrimeProduct

/-! Simultaneous prime divisibility with arbitrary main and error coefficients.

`general_determinant_log_lower_cutoff_congruence` multiplies the local prime-power divisors
of an integer `D` at the good primes up to `x`, together with prescribed divisors at a set
`P` of excluded primes, and bounds `log D` from below. `determinant_log_lower_of_local_divisors`
packages this for a local divisor oracle (for each good prime an exponent with the required
lower bound) and absorbs the square-root error above a cutoff `L ≥ d ^ 4`;
`determinant_log_lower_of_local_divisors_degree_four` is the case `L = 27 d ^ 4`. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real

/-- Prime aggregation from a local divisor oracle. Every prime `p > L` up to `x` outside
`bad` supplies an exponent `e` with `A / mass p - E ≤ e` and `p ^ e ∣ D`, where
`mass p ≤ p + K d² √p` and `d ^ 4 ≤ L`; every `p ∈ P ⊆ bad` contributes `p ^ v p ∣ D`. -/
theorem determinant_log_lower_of_local_divisors {x L K A E : ℝ} {d : ℕ}
    (hx : 1 ≤ x) (hd : 0 < d) (hdL : (d : ℝ) ^ 4 ≤ L) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hE : 0 ≤ E) (bad P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime) (v : ℕ → ℕ)
    (mass : ℕ → ℝ) {D : ℤ} (hD : 0 < D)
    (hmass : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) → 0 < mass p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) →
      mass p ≤ p + K * (d : ℝ) ^ 2 * Real.sqrt p)
    (hlocal : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, L < (p : ℝ) →
      ∃ e : ℕ, A / mass p - E ≤ e ∧ (p : ℤ) ^ e ∣ D)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣ D) :
    A * (Real.log x - Real.log L - 2 * mertensError - (∑ p ∈ bad, Real.log p / p) -
      2 * K * primeBlockMass) - E * ((Real.log 4 + 4) * x) +
      (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤ Real.log D := by
  /- Prescribed primes excluded from the global sum contribute their entire
  local valuation, in addition to the global lower bound. A lower cutoff costs
  `log L`; perturbing `p` by `C √p` costs `O(C / √L)`. -/
  classical
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hL : 1 ≤ L := (one_le_pow₀ hd1).trans hdL
  let G := ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad
  let S := G.filter (fun p : ℕ => L < (p : ℝ))
  let e : ℕ → ℕ := fun p => if h : p ∈ G ∧ L < (p : ℝ) then (hlocal p h.1 h.2).choose else 0
  have hspec (p : ℕ) (hp : p ∈ S) :
      A / mass p - E ≤ e p ∧ (p : ℤ) ^ e p ∣ D := by
    have h : p ∈ G ∧ L < (p : ℝ) := mem_filter.mp hp
    simpa only [e, dite_eq_left h] using (hlocal p h.1 h.2).choose_spec
  have hSP : Disjoint S P := disjoint_left.mpr fun p hpS hpP =>
    (mem_sdiff.mp (mem_filter.mp hpS).1).2 (hPbad hpP)
  let w : ℕ → ℕ := fun p => if p ∈ S then e p else v p
  have hsum : (∑ p ∈ S, (e p : ℝ) * Real.log p) + (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤
      Real.log D := by
    have hh := sum_log_prime_powers_le_log (S ∪ P) w hD
      (fun p h => (mem_union.mp h).elim
        (fun hs => (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hs).1).1).2) (hP p)) fun p h => by
        by_cases hs : p ∈ S
        · simpa only [w, ite_eq_left hs] using (hspec p hs).2
        · simpa only [w, ite_eq_right hs] using hcong p ((mem_union.mp h).resolve_left hs)
    rwa [sum_union hSP,
      sum_congr rfl (fun p hp => by simp only [w, ite_eq_left hp] :
        ∀ p ∈ S, (w p : ℝ) * Real.log p = (e p : ℝ) * Real.log p),
      sum_congr rfl (fun p hp => by
        simp only [w, ite_eq_right (fun h : p ∈ S => disjoint_left.mp hSP h hp)] :
        ∀ p ∈ P, (w p : ℝ) * Real.log p = (v p : ℝ) * Real.log p)] at hh
  have hloc : A * (∑ p ∈ S, Real.log p / mass p) - E * (∑ p ∈ S, Real.log p) ≤
      ∑ p ∈ S, (e p : ℝ) * Real.log p := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact (sum_congr rfl fun p _ => by ring).trans_le (sum_le_sum fun p hp =>
      mul_le_mul_of_nonneg_right (hspec p hp).1 (Real.log_natCast_nonneg p))
  have hm := mul_le_mul_of_nonneg_left
    (weighted_prime_sum_lower_cutoff hx hL (mul_nonneg hK (sq_nonneg (d : ℝ))) bad mass hmass hupper) hA
  have htheta : (∑ p ∈ S, Real.log p) ≤ (Real.log 4 + 4) * x :=
    ((sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans sdiff_subset)
      fun p _ _ => Real.log_natCast_nonneg p).trans (Chebyshev.theta_le_psi x)).trans
      (Chebyshev.psi_le_const_mul_self (by linarith))
  have hsqrt : (d : ℝ) ^ 2 ≤ Real.sqrt L :=
    Real.le_sqrt_of_sq_le (by linarith [show ((d : ℝ) ^ 2) ^ 2 = (d : ℝ) ^ 4 by ring])
  have htail : K * (d : ℝ) ^ 2 * (2 * primeBlockMass / Real.sqrt L) ≤ 2 * K * primeBlockMass := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))).mpr (by
      linarith [mul_le_mul_of_nonneg_left hsqrt
        (mul_nonneg (mul_nonneg zero_le_two hK) primeBlockMass_pos.le)])
  linarith [mul_le_mul_of_nonneg_left htheta hE, mul_le_mul_of_nonneg_left htail hA]

/-- The case `L = 27 d ^ 4` of `determinant_log_lower_of_local_divisors`, with local mass
`p + K d² √p`: the cutoff costs `4 log d + log 27`. -/
theorem determinant_log_lower_of_local_divisors_degree_four {x K A E : ℝ} {d : ℕ}
    (hx : 1 ≤ x) (hd : 0 < d) (hK : 0 ≤ K) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (bad P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime) (v : ℕ → ℕ)
    {D : ℤ} (hD : 0 < D)
    (hlocal : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad, stepanovThreshold (d : ℝ) < p →
      ∃ e : ℕ, A / (p + K * (d : ℝ) ^ 2 * Real.sqrt p) - E ≤ e ∧ (p : ℤ) ^ e ∣ D)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣ D) :
    A * (Real.log x - 4 * Real.log d - Real.log 27 - 2 * mertensError -
      (∑ p ∈ bad, Real.log p / p) - 2 * K * primeBlockMass) -
      E * ((Real.log 4 + 4) * x) + (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤ Real.log D := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have h := determinant_log_lower_of_local_divisors hx hd
    (le_mul_of_one_le_left (by positivity) (by norm_num)) hK hA hE bad P hPbad hP v
    (fun p => p + K * (d : ℝ) ^ 2 * Real.sqrt p) hD
    (fun p hp _ => by
      have hp0 : (0 : ℝ) < p := mod_cast (mem_filter.mp (mem_sdiff.mp hp).1).2.pos
      positivity)
    (fun _ _ _ => le_rfl) hlocal hcong
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
  push_cast at h; linarith

end
end CCDN
