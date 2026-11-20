module

public import GradedNear.SieveBasic

/-!
# The Selberg majorant of `Λ` and the small prime powers

* For `V > 1` and `n ≥ 1`: `Λ(n) ≤ log n · ν_V(n) + [n = p^e, p ≤ V] Λ(n)`. For a prime power
  with `p > V`, every divisor `p^i > 1` has weight `0`, so `ν_V(p^e) = 1`.
* The small-prime powers in `[A,B)` divide the product of the largest power of each
  positive integer `p ≤ V` at most `B`. Summing `Λ` over its divisors gives the logarithm
  of that product.
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

namespace Majorant

/-- If every prime factor of `n ≠ 0` exceeds `V > 1`, then `ν_V(n) = 1`: every divisor `d > 1`
of `n` satisfies `d ≥ minFac n > V`, so only `d = 1` has a nonzero weight, and `ψ_1 = 1`. -/
lemma sieveNu_eq_one_of_lt_minFac {V : ℝ} (hV : 1 < V) {n : ℕ} (hn : n ≠ 0)
    (hmin : V < ((Nat.minFac n : ℕ) : ℝ)) : sieveNu V n = 1 := by
  rw [sieveNu, sum_eq_single_of_mem 1 (Nat.one_mem_divisors.mpr hn)]
  · simp [grahamWeight, hV.le, (Real.log_pos hV).ne']
  · intro d hd hd1
    have hle : (n.minFac : ℝ) ≤ d := by
      exact_mod_cast Nat.minFac_le_of_dvd (by have := Nat.pos_of_mem_divisors hd; omega) (Nat.dvd_of_mem_divisors hd)
    simp [grahamWeight, (hmin.trans_le hle).not_ge]

end Majorant

/-- The Mangoldt mass on powers of primes at most the sieve level. -/
noncomputable def smallPrimeWeight (V : ℝ) (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ (n.minFac : ℝ) ≤ V then Λ n else 0

lemma smallPrimeWeight_nonneg (V : ℝ) (n : ℕ) : 0 ≤ smallPrimeWeight V n := by
  simp [smallPrimeWeight, apply_ite, ArithmeticFunction.vonMangoldt_nonneg]

theorem vonMangoldt_le_sieve {V : ℝ} (hV : 1 < V) (n : ℕ) :
    Λ n ≤ Real.log n * sieveNu V n + smallPrimeWeight V n := by
  have hprod := mul_nonneg (Real.log_natCast_nonneg n) (sieveNu_nonneg V n)
  unfold smallPrimeWeight
  split_ifs with h
  · linarith
  by_cases hpp : IsPrimePow n
  · have hh := lt_of_not_ge (fun hv => h ⟨hpp, hv⟩)
    simpa [Majorant.sieveNu_eq_one_of_lt_minFac hV hpp.ne_zero hh] using
      (ArithmeticFunction.vonMangoldt_le_log (n := n))
  · simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, hprod]

theorem small_primepow_sum {V A B : ℝ} (hV : 0 ≤ V) (hA : 0 < A) (hB : 1 ≤ B) :
    ∑ n ∈ realIco A B, smallPrimeWeight V n / n ≤ V * Real.log B / A := by
  let P := Ioc 0 ⌊V⌋₊
  let f (p : ℕ) := p ^ p.log ⌊B⌋₊
  let N := ∏ p ∈ P, f p
  have hf p (hp : p ∈ P) : f p ≠ 0 := pow_ne_zero _ (mem_Ioc.mp hp).1.ne'
  have hN : N ≠ 0 := prod_ne_zero_iff.mpr hf
  simp_rw [smallPrimeWeight, ite_div, zero_div, ← sum_filter]
  calc
    _ ≤ ∑ n ∈ (realIco A B).filter (fun n => IsPrimePow n ∧ (n.minFac : ℝ) ≤ V), Λ n / A := by
      gcongr with n hn
      exact (mem_realIco.mp (mem_filter.mp hn).1).2.1
    _ ≤ Real.log N / A := by
      rw [← ArithmeticFunction.vonMangoldt_sum, ← sum_div]
      refine div_le_div_of_nonneg_right (sum_le_sum_of_subset_of_nonneg ?_
        fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg) hA.le
      intro n hn
      obtain ⟨hn, hpp, hv⟩ := mem_filter.mp hn
      have hp := Nat.minFac_prime hpp.ne_one
      have hnp : n ≤ ⌊B⌋₊ := Nat.le_floor (mem_realIco.mp hn).2.2.le
      have hd : n ∣ f n.minFac := by
        nth_rewrite 1 [← hpp.minFac_pow_factorization_eq]
        exact pow_dvd_pow _ (Nat.le_log_of_pow_le hp.one_lt (by rwa [hpp.minFac_pow_factorization_eq]))
      exact Nat.mem_divisors.mpr ⟨hd.trans (dvd_prod_of_mem f (mem_Ioc.mpr ⟨hp.pos, Nat.le_floor hv⟩)), hN⟩
    _ ≤ _ := by
      gcongr
      dsimp only [N]
      rw [Nat.cast_prod, Real.log_prod (by simpa using hf)]
      have hB' := (Nat.floor_pos.mpr hB).ne'
      calc
        _ ≤ ∑ p ∈ P, Real.log B := by
          refine sum_le_sum fun p hp => ?_
          exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (hf p hp))
            ((Nat.cast_le.mpr (Nat.pow_log_le_self p hB')).trans (Nat.floor_le (by linarith)))
        _ ≤ _ := by
          simp [P, sum_const]
          exact mul_le_mul_of_nonneg_right (Nat.floor_le hV) (Real.log_nonneg hB)

end GradedNear
