module
public import NearlyMinimax.AliasTailSummation
@[expose] public section
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

variable {P Csharp C mu : ℝ}
def defectTailConstant (Csharp C : ℝ) : ℝ :=
  Real.exp (Csharp * C) * poissonCountWeight (Csharp * C) 2
theorem finite_interpolation_defect_tail_le 
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C) (hmu : 0 < mu)
    (J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (2 + j) ≤ P * C ^ (2 + j) / mu ^ j) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j)) ≤
      defectTailConstant Csharp C * P * mu ^ 2 := by
  have hb (j : ℕ) (hj : j ∈ Finset.range J) :
      poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j) ≤
      P * mu ^ 2 * poissonCountWeight (Csharp * C) (2 + j) := by
    have h := mul_le_mul_of_nonneg_left (hR j hj)
      (poissonCountWeight_nonneg (mul_nonneg hCs hmu.le) (2 + j))
    apply h.trans_eq
    have h_poisson_scaled_defect_identity Csharp C j : poissonCountWeight (Csharp * mu) (2 + j) * C ^ (2 + j) / mu ^ j =
      mu ^ 2 * poissonCountWeight (Csharp * C) (2 + j) := by
      unfold poissonCountWeight
      rw [mul_pow, mul_pow, pow_add mu]
      field_simp
    calc
      _ = P * (poissonCountWeight (Csharp * mu) (2 + j) * C ^ (2 + j) / mu ^ j) := by ring
      _ = _ := by rw [h_poisson_scaled_defect_identity]; ring
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left
    (finite_poissonCountWeight_tail_le (mul_nonneg hCs hC) 2 J)
    (mul_nonneg hP (sq_nonneg mu))
  apply (hs.trans ht).trans_eq
  unfold defectTailConstant
  ring
theorem finite_taylor_count_energy_tail_le 
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (a J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (2 + j) ≤ P * C ^ (2 + j) * (2 + j : ℕ) ^ a) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j)) ≤
      defectTailConstant Csharp (C * 2 ^ a) * P * mu ^ 2 := by
  have h_finite_geometric_count_energy_tail_le {C : ℝ} (hC : 0 ≤ C) (hR : ∀ j ∈ Finset.range J, R (2 + j) ≤ P * C ^ (2 + j)) : (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j)) ≤
      defectTailConstant Csharp C * P * mu ^ 2 := by
    have hb (j : ℕ) (hj : j ∈ Finset.range J) :
        poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j) ≤
        P * mu ^ 2 * poissonCountWeight (Csharp * C) (2 + j) := by
      have h := mul_le_mul_of_nonneg_left (hR j hj)
        (poissonCountWeight_nonneg (mul_nonneg hCs hmu) (2 + j))
      apply h.trans
      have hp : mu ^ (2 + j) ≤ mu ^ 2 := by
        rw [pow_add]
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hmu hmu1) (sq_nonneg mu)).trans_eq (mul_one _)
      have hh := mul_le_mul_of_nonneg_left hp
        (mul_nonneg hP (poissonCountWeight_nonneg (mul_nonneg hCs hC) (2 + j)))
      convert hh using 1 <;> unfold poissonCountWeight <;> simp only [mul_pow] <;> ring
    have hs := Finset.sum_le_sum hb
    rw [← Finset.mul_sum] at hs
    have ht := mul_le_mul_of_nonneg_left
      (finite_poissonCountWeight_tail_le (mul_nonneg hCs hC) 2 J)
      (mul_nonneg hP (sq_nonneg mu))
    apply (hs.trans ht).trans_eq
    unfold defectTailConstant
    ring
  apply h_finite_geometric_count_energy_tail_le (by positivity)
  intro j hj
  apply (hR j hj).trans
  have h := mul_le_mul_of_nonneg_left (polynomial_count_factor_le (2 + j) a)
    (by positivity : 0 ≤ P * C ^ (2 + j))
  simpa only [mul_pow, ← mul_assoc] using h
def fieldTailConstant (Csharp C : ℝ) : ℝ :=
  Real.exp (Csharp * C) * poissonCountWeight (Csharp * C) 4
theorem finite_polynomial_field_count_tail_le 
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (a J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (4 + j) ≤ P * C ^ (4 + j) * (4 + j : ℕ) ^ a) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (4 + j) * R (4 + j)) ≤
      fieldTailConstant Csharp (C * 2 ^ a) * P * mu ^ 4 := by
  have h_finite_geometric_field_count_tail_le {C : ℝ} (hC : 0 ≤ C) (hR : ∀ j ∈ Finset.range J, R (4 + j) ≤ P * C ^ (4 + j)) : (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (4 + j) * R (4 + j)) ≤
      fieldTailConstant Csharp C * P * mu ^ 4 := by
    have hb (j : ℕ) (hj : j ∈ Finset.range J) :
        poissonCountWeight (Csharp * mu) (4 + j) * R (4 + j) ≤
        P * mu ^ 4 * poissonCountWeight (Csharp * C) (4 + j) := by
      have h := mul_le_mul_of_nonneg_left (hR j hj)
        (poissonCountWeight_nonneg (mul_nonneg hCs hmu) (4 + j))
      apply h.trans
      have hp : mu ^ (4 + j) ≤ mu ^ 4 := by
        rw [pow_add]
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hmu hmu1) (pow_nonneg hmu 4)).trans_eq (mul_one _)
      have hh := mul_le_mul_of_nonneg_left hp
        (mul_nonneg hP (poissonCountWeight_nonneg (mul_nonneg hCs hC) (4 + j)))
      convert hh using 1 <;> unfold poissonCountWeight <;> simp only [mul_pow] <;> ring
    have hs := Finset.sum_le_sum hb
    rw [← Finset.mul_sum] at hs
    have ht := mul_le_mul_of_nonneg_left
      (finite_poissonCountWeight_tail_le (mul_nonneg hCs hC) 4 J)
      (mul_nonneg hP (pow_nonneg hmu 4))
    apply (hs.trans ht).trans_eq
    unfold fieldTailConstant
    ring
  apply h_finite_geometric_field_count_tail_le (by positivity)
  intro j hj
  apply (hR j hj).trans
  have h := mul_le_mul_of_nonneg_left (polynomial_count_factor_le (4 + j) a)
    (by positivity : 0 ≤ P * C ^ (4 + j))
  simpa only [mul_pow, ← mul_assoc] using h
end NearlyMinimax
