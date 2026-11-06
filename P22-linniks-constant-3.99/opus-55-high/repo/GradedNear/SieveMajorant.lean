module

public import GradedNear.SieveBasic

/-!
# The Selberg majorant of `Λ` and the small prime powers

* For `V > 1` and `n ≥ 1`: `Λ(n) ≤ log n · ν_V(n) + [n = p^e, p ≤ V] Λ(n)`. For a prime power
  with `p > V`, every divisor `p^i > 1` has weight `0`, so `ν_V(p^e) = 1`.
* The prime powers `n ≥ A` of primes `p ≤ V` contribute `Σ Λ(n)/n ≤ 2 V log V / A`, by the
  geometric series in `e` for each `p ≤ V`.
-/

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

/-- Geometric tail: for `p ≥ 2` and a finite set `F` of exponents with `p^k ≥ A > 0` for all
`k ∈ F`, `Σ_{k ∈ F} p^{-k} ≤ 2/A`. -/
lemma geom_tail {p : ℕ} (hp : 2 ≤ p) {A : ℝ} (hA : 0 < A) (F : Finset ℕ)
    (hF : ∀ k ∈ F, A ≤ (p : ℝ) ^ k) : ∑ k ∈ F, (1 / (p : ℝ)) ^ k ≤ 2 / A := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · positivity
  have hp2 : (2 : ℝ) ≤ p := mod_cast hp
  have := (div_le_one (by positivity)).2 (hF _ (F.min'_mem hne))
  calc _ ≤ ∑ k ∈ Finset.Ico (F.min' hne) (F.max' hne + 1), (1 / (p : ℝ)) ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => Finset.mem_Ico.2
          ⟨F.min'_le k hk, Nat.lt_succ_of_le (F.le_max' k hk)⟩) fun k _ _ => by positivity
    _ ≤ (1 / (p : ℝ)) ^ (F.min' hne) / (1 - 1 / p) :=
        geom_sum_Ico_le_of_lt_one (by positivity) (by rw [div_lt_one] <;> linarith)
    _ ≤ 2 / A := by
      rw [div_le_div_iff₀ (by rw [sub_pos, div_lt_one] <;> linarith) hA, one_div_pow,
        one_div_mul_eq_div]
      have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
      linarith

theorem vonMangoldt_le_sieve {V : ℝ} (hV : 1 < V) (n : ℕ) :
    Λ n ≤ Real.log n * sieveNu V n +
      (if IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V then Λ n else 0) := by
  have := mul_nonneg (Real.log_natCast_nonneg n) (sieveNu_nonneg V n)
  split_ifs with h
  · linarith
  by_cases hpp : IsPrimePow n
  · rw [sieveNu, Finset.sum_eq_single 1 (fun d hd hd1 => ?_)
      fun h => absurd (Nat.one_mem_divisors.2 hpp.ne_zero) h]
    · simpa [grahamWeight, hV.le, (Real.log_pos hV).ne'] using ArithmeticFunction.vonMangoldt_le_log
    have := Nat.minFac_le_of_dvd (by have := Nat.pos_of_mem_divisors hd; omega)
      (Nat.dvd_of_mem_divisors hd)
    rw [grahamWeight, ite_eq_right (not_le.2 ((not_le.1 fun h' => h ⟨hpp, h'⟩).trans_le
      (mod_cast this)))]
  · simpa [ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp]

theorem small_primepow_sum {V A B : ℝ} (hV : 1 ≤ V) (hA : 1 ≤ A) :
    ∑ n ∈ (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter (fun n => IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V),
      Λ n / n ≤ V * (2 * Real.log V / A) := by
  have hA0 : 0 < A := by linarith
  have hlogV := Real.log_nonneg hV
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.Icc 1 ⌊V⌋₊) (g := Nat.minFac) fun n hn =>
    Finset.mem_Icc.2 ⟨Nat.minFac_pos n, Nat.le_floor (Finset.mem_filter.1 hn).2.2⟩]
  refine (Finset.sum_le_card_nsmul _ _ (2 * Real.log V / A) fun p hp => ?_).trans ?_
  · set T := ((Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter
      (fun n => IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V)).filter (fun n => n.minFac = p)
    have hT : ∀ n ∈ T, IsPrimePow n ∧ n.minFac = p ∧ A ≤ n := fun n hn => by
      simp only [T, Finset.mem_filter, Finset.mem_Ico] at hn
      simp_all
    have hpow : ∀ n ∈ T, p ^ n.factorization p = n := fun n hn =>
      (hT n hn).2.1 ▸ (hT n hn).1.minFac_pow_factorization_eq
    rcases T.eq_empty_or_nonempty with h | ⟨n₀, hn₀⟩
    · rw [h, Finset.sum_empty]; positivity
    have hp2 := (hT n₀ hn₀).2.1 ▸ Nat.minFac_prime (hT n₀ hn₀).1.ne_one
    calc _ ≤ ∑ n ∈ T, Real.log V * (1 / (p : ℝ)) ^ n.factorization p :=
          Finset.sum_le_sum fun n hn => by
            rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left (hT n hn).1, (hT n hn).2.1,
              one_div_pow, ← div_eq_mul_one_div, ← Nat.cast_pow, hpow n hn]
            exact div_le_div_of_nonneg_right (Real.log_le_log (mod_cast hp2.pos)
              ((Nat.cast_le.2 (Finset.mem_Icc.1 hp).2).trans (Nat.floor_le (by linarith))))
              (Nat.cast_nonneg _)
      _ ≤ Real.log V * (2 / A) := by
          rw [← Finset.mul_sum, ← Finset.sum_image fun n hn m hm h => by
            rw [← hpow n hn, ← hpow m hm]; exact congrArg (p ^ ·) h]
          exact mul_le_mul_of_nonneg_left (geom_tail hp2.two_le hA0 _ fun k hk => by
            obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hk
            exact_mod_cast (hpow n hn).symm ▸ (hT n hn).2.2) hlogV
      _ = _ := by ring
  · rw [Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
    gcongr
    grind [Nat.floor_le]

end GradedNear
