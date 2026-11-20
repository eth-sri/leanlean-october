module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import DedekindZetaZeroFree.LargeSieve.Exponents.ExponentAndRecursiveEnvelope

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve

theorem crossover_large_scale_bound (α M N : ℝ) (hα : 1 ≤ α) (hα₂ : α ≤ 2)
    (hM : 1 ≤ M) (hN : 1 ≤ N) :
    let β : ℝ := 2 - 1 / α
    (1 ≤ β ∧ β ≤ 2) ∧ 1 ≤ N ^ β ∧ N ≤ N ^ β ∧
      N ^ β * N ≤ (M * N) ^ (3 : ℝ) := by
  have hdiv1 := (div_le_one (lt_of_lt_of_le zero_lt_one hα)).mpr hα
  have hdiv0 : 0 ≤ 1 / α := by positivity
  have hβ1 : 1 ≤ 2 - 1 / α := by linarith
  have hβ2 : 2 - 1 / α ≤ 2 := by linarith
  have hN0 := le_trans zero_le_one hN
  refine ⟨⟨hβ1, hβ2⟩, Real.one_le_rpow hN (le_trans zero_le_one hβ1), ?_, ?_⟩
  · calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ (2 - 1 / α) := Real.rpow_le_rpow_of_exponent_le hN hβ1
  · have h5 : N ^ (2 : ℝ) * N = N ^ (3 : ℝ) := by
      nth_rewrite 2 [← Real.rpow_one N]
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hN)]
      norm_num
    calc _ ≤ N ^ (2 : ℝ) * N := (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN hβ2) hN0)
      _ = N ^ (3 : ℝ) := h5
      _ ≤ (M * N) ^ (3 : ℝ) := (by
        refine Real.rpow_le_rpow hN0 ?_ (by norm_num)
        nlinarith [hM, hN0])

end DedekindZetaZeroFree.LargeSieve
