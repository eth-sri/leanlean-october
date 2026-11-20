module

public import DedekindZetaZeroFree.Arithmetic.Ideals.PrimeFactorDivisorBounds
public import DedekindZetaZeroFree.Analysis.LocalDivisorExponentialBounds

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical

theorem ideal_divisor_count_le_rpow
    (F : Type*) [Field F] [NumberField F] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ A : Ideal (𝓞 F),
      (idealDivisorCount A : ℝ) ≤ C * (Ideal.absNorm A : ℝ) ^ ε := by
  obtain ⟨B, hB1, hB⟩ := DedekindZetaZeroFree.LargeSieve.Vendor.exists_local_exponential_bound ε hε
  have hB0 := le_trans zero_le_one hB1
  set T : ℝ := (2 : ℝ) ^ (1 / ε) with hT
  have hTpos : 0 < T := by rw [hT]; exact Real.rpow_pos_of_pos (by norm_num) _
  set L : ℕ := (boundedNormIdeals F T).card with hL
  have hBL1 : 1 ≤ B ^ L := one_le_pow₀ hB1
  refine ⟨B ^ L, hBL1, fun A => ?_⟩
  by_cases hA : A = ⊥
  · rw [hA]
    simp only [idealDivisorCount, idealDivisors_bot, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (le_trans zero_le_one hBL1) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  let m := UniqueFactorizationMonoid.normalizedFactors A
  let S := m.toFinset
  have htwo : ∀ P ∈ S, (2 : ℝ) ≤ (Ideal.absNorm P : ℝ) := by
    intro P hP
    exact_mod_cast ((two_le_absNorm_of_mem_normalizedFactors A hA) P hP : (2 : ℕ) ≤ Ideal.absNorm P)
  have hfac_small : ∀ P ∈ S, (Ideal.absNorm P : ℝ) ≤ T →
      ((m.count P : ℝ) + 1) ≤ B * ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε := by
    intro P hP _
    refine (hB (m.count P)).trans (mul_le_mul_of_nonneg_left ?_ hB0)
    rw [mul_comm ε (m.count P : ℝ),
      ← Real.rpow_mul (Nat.cast_nonneg (Ideal.absNorm P))]
    exact Real.rpow_le_rpow (by norm_num) (htwo P hP) (mul_nonneg (Nat.cast_nonneg _) hε.le)
  have hfac_large : ∀ P ∈ S, T < (Ideal.absNorm P : ℝ) →
      ((m.count P : ℝ) + 1) ≤ ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε := by
    intro P hP hPT
    have hTeps : T ^ ε = 2 := by
      rw [hT, ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [show 1 / ε * ε = 1 by field_simp, Real.rpow_one]
    have hpow : (2 : ℝ) ≤ (Ideal.absNorm P : ℝ) ^ ε := by
      have hlt :=
        Real.rpow_lt_rpow hTpos.le hPT hε
      rw [hTeps] at hlt
      exact hlt.le
    calc _ ≤ (Ideal.absNorm P : ℝ) ^ (ε * (m.count P : ℝ)) := (DedekindZetaZeroFree.LargeSieve.Vendor.local_exponential_bound_of_two_le_rpow ε (Ideal.absNorm P : ℝ)
      (le_trans (by norm_num) (htwo P hP)) hpow (m.count P))
      _ = ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε := by
          rw [mul_comm ε (m.count P : ℝ),
            Real.rpow_mul (Nat.cast_nonneg (Ideal.absNorm P))]
  have hg_nonneg : ∀ P, (0 : ℝ) ≤ ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε :=
    fun P => Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
  have hsmall :
      (∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T), ((m.count P : ℝ) + 1)) ≤
      B ^ L * (∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T),
        ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε) := by
    calc (∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T), ((m.count P : ℝ) + 1))
        ≤ ∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T),
            B * ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε := (Finset.prod_le_prod₀ (fun P _ => by positivity) (fun P hP => by
              rw [Finset.mem_filter] at hP
              exact hfac_small P hP.1 hP.2))
      _ = (∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T), B) *
            (∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T),
              ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε) :=
            Finset.prod_mul_distrib
      _ = B ^ (S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T)).card *
            (∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T),
              ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε) := by
            rw [Finset.prod_const]
      _ ≤ B ^ L * (∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T),
              ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε) := by
            apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun P _ => hg_nonneg P))
            exact pow_le_pow_right₀ hB1 (Finset.card_le_card (fun P hP => by
              rw [Finset.mem_filter] at hP
              rw [mem_boundedNormIdeals]
              exact hP.2))
  have hprod : (∏ P ∈ S, ((m.count P : ℝ) + 1)) ≤
      B ^ L * (∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε) := by
    rw [((Finset.prod_filter_mul_prod_filter_not S (fun P => (Ideal.absNorm P : ℝ) ≤ T)
      (fun P => ((m.count P : ℝ) + 1))).symm)]
    calc (∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T), ((m.count P : ℝ) + 1)) *
          (∏ P ∈ S.filter (fun P => ¬ (Ideal.absNorm P : ℝ) ≤ T), ((m.count P : ℝ) + 1))
        ≤ (B ^ L * (∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T),
              ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε)) *
          (∏ P ∈ S.filter (fun P => ¬ (Ideal.absNorm P : ℝ) ≤ T),
              ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε) :=
          mul_le_mul hsmall (Finset.prod_le_prod₀ (fun P _ => by positivity) (fun P hP => by
            rw [Finset.mem_filter] at hP
            exact hfac_large P hP.1 (lt_of_not_ge hP.2)))
            (Finset.prod_nonneg (fun P _ => by positivity))
            (mul_nonneg (pow_nonneg hB0 _) (Finset.prod_nonneg (fun P _ => hg_nonneg P)))
      _ = B ^ L * ((∏ P ∈ S.filter (fun P => (Ideal.absNorm P : ℝ) ≤ T),
              ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε) *
          (∏ P ∈ S.filter (fun P => ¬ (Ideal.absNorm P : ℝ) ≤ T),
              ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε)) := by ring
      _ = B ^ L * (∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε) := by
          rw [Finset.prod_filter_mul_prod_filter_not S (fun P => (Ideal.absNorm P : ℝ) ≤ T)
            (fun P => ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε)]
  have hnormprod : (∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ))) = (Ideal.absNorm A : ℝ) := by
    rw [(absNorm_eq_prod_normalizedFactors_counts A hA), Nat.cast_prod]
    refine Finset.prod_congr rfl (fun P _ => ?_)
    rw [Nat.cast_pow, Real.rpow_natCast]
  calc _ ≤ ∏ P ∈ S, ((m.count P : ℝ) + 1) := (idealDivisorCount_le_normalizedFactors_box A hA)
    _ ≤ B ^ L * (∏ P ∈ S, ((Ideal.absNorm P : ℝ) ^ (m.count P : ℝ)) ^ ε) := hprod
    _ = B ^ L * (Ideal.absNorm A : ℝ) ^ ε := by
        rw [Real.finsetProd_rpow S (fun P => (Ideal.absNorm P : ℝ) ^ (m.count P : ℝ))
          (fun P _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) ε, hnormprod]

end DedekindZetaZeroFree.LargeSieve
