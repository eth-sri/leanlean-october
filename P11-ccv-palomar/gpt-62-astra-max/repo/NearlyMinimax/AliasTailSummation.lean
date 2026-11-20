module

public import NearlyMinimax.PoissonEnergyBounds


@[expose] public section

/-! Finite alias factorial tails, including absorption of exp(C*M) into the
fixed factorial-tail constant. This does not enlarge the activity exponent. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

variable {A x y P Csharp C L : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (k a : ℕ) {mu : ℝ} (hA : 0 ≤ A) (hP : 0 ≤ P)
    (hCs : 0 ≤ Csharp) (hC : 0 ≤ C) (hL : 0 ≤ L) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (M J : ℕ)

include hx hxy in
theorem poissonCountWeight_mono :
    poissonCountWeight x k ≤ poissonCountWeight y k := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy k) (Nat.cast_nonneg _)

include hx in
theorem finite_poissonCountWeight_tail_le :
    (∑ j ∈ Finset.range J, poissonCountWeight x (a + j)) ≤
      Real.exp x * poissonCountWeight x a := (((poissonCountWeight_summable x).comp_injective (fun _ _ h => Nat.add_left_cancel h)).sum_le_tsum _ (fun j _ => poissonCountWeight_nonneg hx _)).trans
    (poissonCountWeight_tail_le hx a)

def aliasTailConstant (A Csharp C L : ℝ) : ℝ :=
  1 + A * Real.exp (Csharp * C) + Csharp * C * Real.exp L

include hA hCs hC in
theorem aliasTailConstant_ge_one :
    1 ≤ aliasTailConstant A Csharp C L := by
  unfold aliasTailConstant
  have h1 : 0 ≤ A * Real.exp (Csharp * C) := by positivity
  have h2 : 0 ≤ Csharp * C * Real.exp L := by positivity
  bound

include hCs hC in
theorem aliasTailConstant_ge_prefactor :
    A * Real.exp (Csharp * C) ≤ aliasTailConstant A Csharp C L := by
  unfold aliasTailConstant
  have h : 0 ≤ Csharp * C * Real.exp L := by positivity
  linarith only [h]

include hx hL in
theorem poissonCountWeight_exp_absorption :
    Real.exp (L * M) * poissonCountWeight x (M + 1) ≤
      poissonCountWeight (x * Real.exp L) (M + 1) := by
  have he : Real.exp (L * M) ≤ Real.exp (L * (M + 1)) := by
    bound
  have h := mul_le_mul_of_nonneg_right he (poissonCountWeight_nonneg hx (M + 1))
  have heq : Real.exp (L * (M + 1)) = Real.exp L ^ (M + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [heq] at h
  simpa only [poissonCountWeight, mul_pow, div_eq_mul_inv, mul_assoc, mul_left_comm] using h

include hA hP hCs hC hL hmu hmu1 in
/-- Actual count energies may be supplied only on the finite selected tail.
The fixed constant is chosen before M and the number of counted terms. -/
theorem finite_alias_energy_tail_le (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (M + 1 + j) ≤
      A * P * Real.exp (L * M) * C ^ (M + 1 + j)) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (M + 1 + j) * R (M + 1 + j)) ≤
      aliasTailConstant A Csharp C L * P *
        poissonCountWeight (aliasTailConstant A Csharp C L * mu) (M + 1) := by
  let K := aliasTailConstant A Csharp C L
  have hK1 : 1 ≤ K := aliasTailConstant_ge_one hA hCs hC
  have hK0  := (by norm_num : (0 : ℝ) ≤ 1).trans hK1
  have hb j (hj : j ∈ Finset.range J) :
      poissonCountWeight (Csharp * mu) (M + 1 + j) * R (M + 1 + j) ≤
      (A * P * Real.exp (L * M)) * poissonCountWeight (Csharp * C * mu) (M + 1 + j) := by
    have h := mul_le_mul_of_nonneg_left (hR j hj)
      (poissonCountWeight_nonneg (mul_nonneg hCs hmu) (M + 1 + j))
    convert h using 1 <;> unfold poissonCountWeight <;> rw [mul_pow] <;> ring
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have ht := finite_poissonCountWeight_tail_le (by positivity : 0 ≤ Csharp * C * mu) (M + 1) J
  have hm := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ A * P * Real.exp (L * M))
  have hexp : Real.exp (Csharp * C * mu) ≤ Real.exp (Csharp * C) :=
    by bound
  have hbase : Csharp * C * Real.exp L * mu ≤ K * mu :=
    mul_le_mul_of_nonneg_right ((by unfold aliasTailConstant; bound : Csharp * C * Real.exp L ≤ aliasTailConstant A Csharp C L)) hmu
  calc
    _ ≤ _ := hs.trans hm
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hexp (poissonCountWeight_nonneg (by positivity) _)) (by positivity)
    _ = (A * Real.exp (Csharp * C) * P) *
        (Real.exp (L * M) * poissonCountWeight (Csharp * C * mu) (M + 1)) := by ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (poissonCountWeight_exp_absorption (by positivity) hL M) (by positivity)
    _ ≤ _ := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_right (aliasTailConstant_ge_prefactor hCs hC) hP)
        (poissonCountWeight_mono (by positivity) (by nlinarith only [hbase]) _)
        (poissonCountWeight_nonneg (by positivity) _)
        (mul_nonneg hK0 hP)
    _ = _ := rfl

end NearlyMinimax
