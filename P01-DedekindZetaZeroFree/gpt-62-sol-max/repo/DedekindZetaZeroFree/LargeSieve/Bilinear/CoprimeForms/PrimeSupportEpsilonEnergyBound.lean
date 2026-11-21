module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.CoprimeForms.WeightedEnergyAndPrimeSupportCost
public import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds

public import DedekindZetaZeroFree.Arithmetic.Ideals.PrimeSupportCost

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

open scoped NumberField Classical

theorem support_cost_energy_bound
    (F : Type) [Field F] [NumberField F] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : Ideal (𝓞 F)) (N X : ℝ), 1 ≤ N → 0 < X → X ≤ N →
      ∀ alpha : Ideal (𝓞 F) → ℂ,
        (∑ u ∈ paperShell F c X, primeSupportCost u * ‖alpha u‖ ^ 2) ≤
          C * Real.rpow N ε * energy F c X alpha := by
  obtain ⟨C₀, hC₀1, hC₀⟩ := DedekindZetaZeroFree.LargeSieve.ideal_divisor_count_le_rpow F ε hε
  refine ⟨C₀ * Real.rpow 2 ε, mul_nonneg (le_trans zero_le_one hC₀1)
    (Real.rpow_nonneg (by norm_num) ε), ?_⟩
  intro c N X hN hX hXN alpha
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hC₀0 : (0 : ℝ) ≤ C₀ := le_trans zero_le_one hC₀1
  have hterm : ∀ u ∈ paperShell F c X,
      primeSupportCost u * ‖alpha u‖ ^ 2 ≤
        (C₀ * Real.rpow 2 ε * Real.rpow N ε) * ‖alpha u‖ ^ 2 := by
    intro u hu
    have hmem := (mem_paperShell F c X u).mp hu
    have hune : u ≠ ⊥ := by
      have := hmem.1.ne_zero
      simpa [Ideal.zero_eq_bot] using this
    have hnormle : (Ideal.absNorm u : ℝ) ≤ 2 * N := by
      have h2 : (Ideal.absNorm u : ℝ) ≤ 2 * X := hmem.2.2.2
      nlinarith [hXN]
    have hrpow : (Ideal.absNorm u : ℝ) ^ ε ≤ (2 * N) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hnormle hε.le
    have hcost : primeSupportCost u ≤ C₀ * Real.rpow 2 ε * Real.rpow N ε := by
      calc primeSupportCost u ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisorCount u : ℝ) :=
            primeSupportCost_le_divisorCount u hune
        _ ≤ C₀ * (Ideal.absNorm u : ℝ) ^ ε := hC₀ u
        _ ≤ C₀ * (2 * N) ^ ε := mul_le_mul_of_nonneg_left hrpow hC₀0
        _ = C₀ * Real.rpow 2 ε * Real.rpow N ε := by
              rw [Real.mul_rpow (by norm_num) hNpos.le, mul_assoc]
              rfl
    exact mul_le_mul_of_nonneg_right hcost (sq_nonneg _)
  calc (∑ u ∈ paperShell F c X, primeSupportCost u * ‖alpha u‖ ^ 2)
      ≤ ∑ u ∈ paperShell F c X,
          (C₀ * Real.rpow 2 ε * Real.rpow N ε) * ‖alpha u‖ ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (C₀ * Real.rpow 2 ε * Real.rpow N ε) * energy F c X alpha := by
        simp only [energy, Finset.mul_sum]

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdTail

end
