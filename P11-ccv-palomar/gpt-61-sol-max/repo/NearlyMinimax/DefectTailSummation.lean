module

public import NearlyMinimax.AliasTailSummation

@[expose] public section

/-! Finite factorial summation of interpolation and Taylor count defects,
with constants independent of the sample size and the selected count cutoff. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

def defectTailConstant Csharp C  :=
  Real.exp (Csharp * C) * poissonCountWeight (Csharp * C) 2

theorem poisson_scaled_defect_identity {mu } (hmu : 0 < mu)
    Csharp C j :
    poissonCountWeight (Csharp * mu) (2 + j) * C ^ (2 + j) / mu ^ j =
      mu ^ 2 * poissonCountWeight (Csharp * C) (2 + j) := by
  unfold poissonCountWeight
  rw [mul_pow, mul_pow, pow_add mu]
  field_simp

section
variable {P Csharp C mu : ℝ} (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
include hP hCs hC

/-- The inverse occupancy factor in the genuine interpolation deficit is
cancelled before the finite factorial series is summed. -/
theorem finite_interpolation_defect_tail_le  (hmu : 0 < mu)
    J (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (2 + j) ≤ P * C ^ (2 + j) / mu ^ j) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j)) ≤
      defectTailConstant Csharp C * P * mu ^ 2 := by
  have hb (j : ℕ) (hj : j ∈ Finset.range J) :
      poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j) ≤
      P * mu ^ 2 * poissonCountWeight (Csharp * C) (2 + j) := by
    have h := mul_le_mul_of_nonneg_left (hR j hj)
      (poissonCountWeight_nonneg (mul_nonneg hCs hmu.le) (2 + j))
    apply h.trans_eq
    calc
      _ = P * (poissonCountWeight (Csharp * mu) (2 + j) * C ^ (2 + j) / mu ^ j) := by ring
      _ = _ := by rw [poisson_scaled_defect_identity hmu]; ring
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left
    (finite_poissonCountWeight_tail_le (mul_nonneg hCs hC) 2 J)
    (mul_nonneg hP (sq_nonneg mu))
  apply (hs.trans ht).trans_eq
  unfold defectTailConstant
  ring

section
variable (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
include hmu hmu1

theorem finite_geometric_count_energy_tail_le 
     J (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (2 + j) ≤ P * C ^ (2 + j)) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j)) ≤
      defectTailConstant Csharp C * P * mu ^ 2 := by
  have hb (j : ℕ) (hj : j ∈ Finset.range J) :
      poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j) ≤
      P * mu ^ 2 * poissonCountWeight (Csharp * C) (2 + j) := by
    have h := mul_le_mul_of_nonneg_left (hR j hj)
      (poissonCountWeight_nonneg (mul_nonneg hCs hmu) (2 + j))
    apply h.trans
    have hp : mu ^ (2 + j) ≤ mu ^ 2 := by
      bound
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

/-- The actual fixed-order Taylor derivative factor k^a is absorbed into a
fixed geometric count factor before applying the same genuine series bound. -/
theorem finite_taylor_count_energy_tail_le 
     a J (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (2 + j) ≤ P * C ^ (2 + j) * (2 + j : ℕ) ^ a) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j)) ≤
      defectTailConstant Csharp (C * 2 ^ a) * P * mu ^ 2 := by
  apply finite_geometric_count_energy_tail_le hP hCs (by positivity) hmu hmu1 J R
  intro j hj
  apply (hR j hj).trans
  have h := mul_le_mul_of_nonneg_left (polynomial_count_factor_le (2 + j) a)
    (by positivity : 0 ≤ P * C ^ (2 + j))
  simpa only [mul_pow, ← mul_assoc] using h
end

end


end NearlyMinimax
