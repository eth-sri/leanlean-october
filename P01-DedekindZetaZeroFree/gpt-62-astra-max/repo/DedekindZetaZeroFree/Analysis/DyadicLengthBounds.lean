module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character
public import DedekindZetaZeroFree.Analysis.DyadicLength

@[expose] public section

/-
https://github.com/openai/math
Revision: adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Source: lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DyadicColumns.lean.
-/

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor

theorem dyadicLength_cover (X : ℝ) : X ≤ (2 : ℝ) ^ dyadicLength X := by
  rcases lt_or_ge X 1 with hX | hX
  · exact (le_of_lt hX).trans (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  · calc X = Real.exp (Real.log X) := (Real.exp_log (lt_of_lt_of_le zero_lt_one hX)).symm
      _ ≤ Real.exp (Real.log ((2 : ℝ) ^ dyadicLength X)) := Real.exp_le_exp.2 (by
        rw [Real.log_pow]; exact ((div_le_iff₀ (Real.log_pos one_lt_two)).1 (by
          rw [dyadicLength]; exact Nat.le_ceil _)))
      _ = (2 : ℝ) ^ dyadicLength X := Real.exp_log (by positivity)

theorem pow_lt_of_lt_dyadicLength {X : ℝ} (hX : 1 ≤ X) {k : ℕ}
    (hk : k < dyadicLength X) : (2 : ℝ) ^ k < X := by
  refine (Real.log_lt_log_iff (by positivity) (lt_of_lt_of_le zero_lt_one hX)).1 ?_
  rw [Real.log_pow]; exact ((lt_div_iff₀ (Real.log_pos one_lt_two)).1 (by
  rw [dyadicLength] at hk; exact (Nat.lt_ceil).1 hk))

theorem dyadicLength_small_power_constant_pos {η : ℝ} (hη : 0 < η) :
    0 < 2 + 1 / (η * Real.log 2) := by
  have := one_div_pos.2 (mul_pos hη (Real.log_pos one_lt_two))
  linarith

theorem dyadicLength_small_power {η X : ℝ} (hη : 0 < η) (hX : 1 ≤ X) :
    (dyadicLength X + 1 : ℝ) ≤ (2 + 1 / (η * Real.log 2)) * X ^ η := by
  have hlog2 := Real.log_pos one_lt_two
  have hXη := Real.one_le_rpow hX hη.le
  have hceil : (dyadicLength X : ℝ) < Real.log X / Real.log 2 + 1 := by
    rw [dyadicLength]; exact Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hX) hlog2.le)
  have hlog_le := Real.log_le_rpow_div (lt_of_lt_of_le zero_lt_one hX).le hη
  have hdiv : Real.log X / Real.log 2 ≤ X ^ η / (η * Real.log 2) := by
    have := div_le_div_of_nonneg_right hlog_le hlog2.le
    rwa [div_div] at this
  have hfinal : X ^ η / (η * Real.log 2) + 2 * X ^ η
      = (2 + 1 / (η * Real.log 2)) * X ^ η := by
    have hne := ne_of_gt (mul_pos hη hlog2)
    field_simp
    ring
  calc (dyadicLength X + 1 : ℝ) = (dyadicLength X : ℝ) + 1 := by push_cast; ring
    _ ≤ X ^ η / (η * Real.log 2) + 2 * X ^ η := by linarith
    _ = (2 + 1 / (η * Real.log 2)) * X ^ η := hfinal

end DedekindZetaZeroFree.LargeSieve.Vendor
