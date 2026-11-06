/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Combining local divisibility at distinct primes

Local powers of different primes multiply, and their weighted logarithms give a lower
bound on the logarithm of a positive determinant gcd. Estimating these prime sums uniformly
for curve reductions is a separate part of CCDN Proposition 3.2.6.
-/

@[expose] public section

namespace CCDN

/-- If each prime `p` in the finite set `P` has `p ^ e p` dividing the positive integer `D`,
then `∑ p ∈ P, e p * log p ≤ log D`. -/
theorem sum_log_prime_powers_le_log (P : Finset ℕ) (e : ℕ → ℕ) {D : ℤ}
    (hD : 0 < D) (hP : ∀ p ∈ P, Nat.Prime p)
    (hdiv : ∀ p ∈ P, (p : ℤ) ^ e p ∣ D) :
    (∑ p ∈ P, (e p : ℝ) * Real.log p) ≤ Real.log D := by
  have hdvd : (∏ p ∈ P, (p : ℤ) ^ e p) ∣ D := Finset.prod_dvd_of_coprime
    (fun p hp q hq hpq => (Nat.isCoprime_iff_coprime.mpr
      ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)).pow) hdiv
  have hpR (p : ℕ) (hp : p ∈ P) : 0 < (p : ℝ) ^ e p := pow_pos (mod_cast (hP p hp).pos) _
  simpa [Real.log_prod fun p hp => (hpR p hp).ne'] using
    Real.log_le_log (Finset.prod_pos hpR) (by exact_mod_cast Int.le_of_dvd hD hdvd)

end CCDN
