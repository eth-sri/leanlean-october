module

public import NearlyMinimax.AliasTailSummation

@[expose] public section

/-! Factorial summation of interpolation defects and higher-field terms.
The starting count sets the leading occupancy power. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

def countTailConstant (k : ℕ) (Csharp C : ℝ) : ℝ :=
  Real.exp (Csharp * C) * poissonCountWeight (Csharp * C) k

abbrev defectTailConstant := countTailConstant 2
abbrev fieldTailConstant := countTailConstant 4

theorem finite_scaled_count_tail_le {P Csharp C μ σ : ℝ}
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C) (hμ : 0 ≤ μ)
    (hσ : 0 < σ) (hμσ : μ ≤ σ) (k J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (k + j) ≤ P * C ^ (k + j) / σ ^ j) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * μ) (k + j) * R (k + j)) ≤
      countTailConstant k Csharp C * P * μ ^ k := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range J) :
      poissonCountWeight (Csharp * μ) (k + j) * R (k + j) ≤
        (P * μ ^ k) * poissonCountWeight (Csharp * C) (k + j) := by
    calc
      _ ≤ poissonCountWeight (Csharp * μ) (k + j) * (P * C ^ (k + j) / σ ^ j) :=
        mul_le_mul_of_nonneg_left (hR j hj) (poissonCountWeight_nonneg (by positivity) _)
      _ = ((P * μ ^ k) * poissonCountWeight (Csharp * C) (k + j)) * (μ / σ) ^ j := by
        unfold poissonCountWeight
        rw [mul_pow, mul_pow, pow_add μ, div_pow]
        ring
      _ ≤ _ := mul_le_of_le_one_right
        (mul_nonneg (by positivity) (poissonCountWeight_nonneg (by positivity) _))
        (pow_le_one₀ (by positivity) ((div_le_one hσ).2 hμσ))
  have hs := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hs
  refine (hs.trans (mul_le_mul_of_nonneg_left (finite_poissonCountWeight_tail_le (by positivity) k J)
    (by positivity))).trans_eq ?_
  unfold countTailConstant
  ring

section
variable {P Csharp C μ : ℝ}
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
include hP hCs hC

/-- The inverse occupancy in the interpolation deficit cancels in the Poisson weights. -/
theorem finite_interpolation_defect_tail_le (hμ : 0 < μ) (J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (2 + j) ≤ P * C ^ (2 + j) / μ ^ j) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * μ) (2 + j) * R (2 + j)) ≤
      defectTailConstant Csharp C * P * μ ^ 2 :=
  finite_scaled_count_tail_le hP hCs hC hμ.le hμ le_rfl 2 J R hR

/-- A fixed polynomial factor in the count is absorbed into the geometric base. -/
theorem finite_polynomial_count_tail_le (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (k a J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (k + j) ≤ P * C ^ (k + j) * (k + j : ℕ) ^ a) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * μ) (k + j) * R (k + j)) ≤
      countTailConstant k Csharp (C * 2 ^ a) * P * μ ^ k := by
  refine finite_scaled_count_tail_le hP hCs (by positivity) hμ zero_lt_one hμ1 k J R fun j hj => ?_
  apply (hR j hj).trans
  have h := mul_le_mul_of_nonneg_left (polynomial_count_factor_le (k + j) a)
    (by positivity : 0 ≤ P * C ^ (k + j))
  simpa only [one_pow, div_one, mul_pow, ← mul_assoc] using h

end

end NearlyMinimax
