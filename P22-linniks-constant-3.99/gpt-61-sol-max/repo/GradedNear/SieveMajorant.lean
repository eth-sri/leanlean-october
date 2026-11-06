import GradedNear.Tactics

import GradedNear.SieveBasic

/-!
# The Selberg majorant of `Λ` and the small prime powers

* For `V > 1` and `n ≥ 1`: `Λ(n) ≤ log n · ν_V(n) + [n = p^e, p ≤ V] Λ(n)`. For a prime power
  with `p > V`, every divisor `p^i > 1` has weight `0`, so `ν_V(p^e) = 1`.
* The prime powers `n ≥ A` of primes `p ≤ V` contribute `Σ Λ(n)/n ≤ 2 V log V / A`, by the
  geometric series in `e` for each `p ≤ V`.
-/

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

theorem vonMangoldt_le_sieve {V : ℝ} (hV : 1 < V) (n : ℕ) :
    Λ n ≤ Real.log n * sieveNu V n +
       if IsPrimePow n ∧ ↑ (Nat.minFac n) ≤ V then Λ n else 0 := by
  have hprod : 0 ≤ Real.log n * sieveNu V n := by positivity
  by_cases hpp : IsPrimePow n
  · by_cases hmin : ↑ (Nat.minFac n) ≤ V
    · simp_all
    · have hnu : sieveNu V n = 1 := by
        have hsum : ∑ d ∈ n.divisors, grahamWeight V d = 1 := by
          rw [Finset.sum_eq_single 1]
          · have hlog := (Real.log_pos hV).ne'
            simp [grahamWeight, hV.le, hlog]
          · intro d hd hd1
            have hdpos := Nat.pos_of_mem_divisors hd
            have hd2 : 2 ≤ d := by omega
            have hle := Nat.minFac_le_of_dvd hd2 (Nat.dvd_of_mem_divisors hd)
            have hle' : (Nat.minFac n : ℝ) ≤ d := by simp_all
            grind [grahamWeight]
          simp_all [hpp.ne_zero]
        simp [sieveNu, hsum]
      rw [ite_eq_right fun h => hmin h.2 , add_zero, hnu, mul_one]
      exact ArithmeticFunction.vonMangoldt_le_log
  · rwa [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, ite_eq_right fun h => hpp h.1 ,
      add_zero]

theorem small_primepow_sum {V A B : ℝ} (hV : 1 ≤ V) (hA : 1 ≤ A) :
    ∑ n ∈ (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter fun n => IsPrimePow n ∧ ↑ (Nat.minFac n) ≤ V ,
      Λ n / n ≤ 2 * V * Real.log V / A := by
  have hA0 : 0 < A := by linarith
  have fiber_bound (p : ℕ) (T : Finset ℕ)
      (hT : ∀ n ∈ T, IsPrimePow n ∧ Nat.minFac n = p ∧ A ≤ n) :
      ∑ n ∈ T, Λ n / n ≤ 2 * Real.log p / A := by

    rcases T.eq_empty_or_nonempty with h | ⟨n₀, hn₀⟩
    · rw [h]
      positivity
    have hp : p.Prime := by
      obtain ⟨hpp, hmin, _⟩ := hT n₀ hn₀
      rw [← hmin]
      exact Nat.minFac_prime hpp.ne_one
    have hpow : ∀ n ∈ T, p ^ n.factorization p = n := by
      grind [IsPrimePow.minFac_pow_factorization_eq]

    let F := T.image fun n : ℕ => n.factorization p
    have hF : ∀ k ∈ F, A ≤ ↑p ^ k := by
      rintro k hk
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hk
      rw [← Nat.cast_pow, hpow n hn]
      exact (hT n hn).2.2
    have hne : F.Nonempty := ⟨_, Finset.mem_image_of_mem _ hn₀⟩

    calc ∑ n ∈ T, Λ n / n =
          Real.log p * ∑ k ∈ F, 1 / ↑p ^ k := by
            rw [Finset.sum_image (Set.LeftInvOn.injOn hpow), Finset.mul_sum]
            congr! 1 with n hn
            obtain ⟨hpp, hmin, _⟩ := hT n hn
            rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left hpp, hmin, ← Nat.cast_pow, hpow n hn]
            ring
      _ ≤ Real.log p * (2 / A) :=
          mul_le_mul_of_nonneg_left (by
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
            have hm := F.min'_mem hne

            have hx0 : (0 : ℝ) ≤ 1 / p := by positivity
            have hx1 : 1 / (p : ℝ) ≤ 1 / 2 := by bound
            calc ∑ k ∈ F, 1 / ↑p ^ k = ∑ k ∈ F, (1 / ↑p) ^ k :=
                  Finset.sum_congr rfl fun k _ => (one_div_pow (p : ℝ) k).symm
              _ ≤ ∑ k ∈ Finset.Ico (F.min' hne) (F.max' hne + 1), (1 / (p : ℝ)) ^ k :=
                  Finset.sum_le_sum_of_subset_of_nonneg (by
                    grind [Finset.min'_le, Finset.le_max']
                  ) fun k _ _ => pow_nonneg hx0 k
              _ ≤ (1 / ↑p) ^ F.min' hne / (1 - 1 / ↑p) :=
                  geom_sum_Ico_le_of_lt_one hx0 (by linarith)
              _ ≤ 2 * (1 / ↑p) ^ F.min' hne := by
                  rw [div_le_iff₀ (by linarith)]
                  nlinarith [pow_nonneg hx0 (F.min' hne)]
              _ = 2 / ↑p ^ F.min' hne := by ring
              _ ≤ 2 / A := div_le_div_of_nonneg_left (by norm_num) hA0 (hF _ hm)
          ) (Real.log_natCast_nonneg p)
      _ = 2 * Real.log p / A := by ring

  have hlogV := Real.log_nonneg hV

  rw [← Finset.sum_fiberwise_of_maps_to (by
    intro n hn
    rw [Finset.mem_filter] at hn
    exact Finset.mem_Icc.mpr ⟨Nat.minFac_pos n, Nat.le_floor hn.2.2⟩
  )]
  calc _ ≤ ∑ p ∈ Finset.Icc 1 ⌊V⌋₊, 2 * Real.log p / A := by
        gcongr 1 with p _
        apply fiber_bound p
        simp_all
    _ ≤ ∑ p ∈ Finset.Icc 1 ⌊V⌋₊, 2 * Real.log V / A := by
        gcongr 1 with p hp
        rw [Finset.mem_Icc] at hp
        have hp0 : (0 : ℝ) < p := by aesop
        have hpV := (Nat.cast_le.mpr hp.2).trans (Nat.floor_le (by linarith))
        gcongr
    _ = ↑ ⌊V⌋₊ * (2 * Real.log V / A) := by simp_all
    _ ≤ V * (2 * Real.log V / A) := by
        apply mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith))
        positivity
    _ = 2 * V * Real.log V / A := by ring

end GradedNear
