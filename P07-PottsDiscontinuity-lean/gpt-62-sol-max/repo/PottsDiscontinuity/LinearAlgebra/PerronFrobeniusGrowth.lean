module

public import PottsDiscontinuity.LinearAlgebra.PerronFrobeniusIrreducible

/-! Trace growth via even powers and a positive diagonal. -/

@[expose] public section

open Matrix Finset Filter Topology
namespace PottsDiscontinuity.PerronFrobenius

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℝ}

/-- The spectral theorem bounds the trace by the dimension times the Perron power. -/
theorem trace_pow_le_card_mul_pfRoot_pow (hA : A.IsHermitian)
    (hnn : ∀ i j, 0 ≤ A i j) (M : ℕ) :
    (A ^ M).trace ≤ (Fintype.card ι : ℝ) * pfRoot A ^ M := by
  rw [trace_pow_eq_sum hA, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_le_sum fun i _ => (by simpa using le_abs_self (hA.eigenvalues i ^ M) :
    hA.eigenvalues i ^ M ≤ |hA.eigenvalues i| ^ M).trans
    (pow_le_pow_left₀ (abs_nonneg _) (abs_eigenvalues_le_pfRoot hA hnn i) _)

theorem trace_pow_mono (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 1 ≤ A i i) (M : ℕ) :
    (A ^ M).trace ≤ (A ^ (M + 1)).trace := by
  exact Finset.sum_le_sum fun i _ =>
    (le_mul_of_one_le_right (Matrix.pow_apply_nonneg hnn M i i) (hd i)).trans
      (Finset.single_le_sum (fun j _ => mul_nonneg (Matrix.pow_apply_nonneg hnn M i j)
        (hnn j i)) (mem_univ i))

/-- A positive diagonal keeps the even-power trace lower bound from vanishing at odd powers. -/
theorem trace_pow_lower (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 1 ≤ A i i) (hρ : 0 < pfRoot A) (M : ℕ) :
    min 1 (pfRoot A)⁻¹ * pfRoot A ^ M ≤ (A ^ M).trace := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq_pfRoot hA
  have hev (m : ℕ) : pfRoot A ^ (2 * m) ≤ (A ^ (2 * m)).trace := by
    rw [trace_pow_eq_sum hA, ← hi]
    exact Finset.single_le_sum (f := fun j => hA.eigenvalues j ^ (2 * m))
      (fun j _ => by rw [pow_mul]; positivity) (mem_univ i)
  obtain ⟨m, h | h⟩ := Nat.even_or_odd' M
  · subst M
    exact (mul_le_of_le_one_left (by positivity) (min_le_left ..)).trans (hev m)
  · subst M
    refine le_trans ?_ ((hev m).trans (trace_pow_mono hnn hd _))
    calc
      _ ≤ (pfRoot A)⁻¹ * pfRoot A ^ (2 * m + 1) := by gcongr; exact min_le_right ..
      _ = _ := by rw [pow_succ]; field_simp

theorem tendsto_scaled_log_mul_pow {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (C * ρ ^ M)) atTop (𝓝 (Real.log ρ)) := by
  have ht := (tendsto_one_div_atTop_nhds_zero_nat.mul_const (Real.log C)).add_const (Real.log ρ)
  apply (show Tendsto _ atTop (𝓝 (Real.log ρ)) by simpa using ht).congr'
  filter_upwards [eventually_gt_atTop 0] with M hM
  have hM' : (M : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul hC.ne' (pow_ne_zero _ hρ.ne'), Real.log_pow]
  field_simp

theorem tendsto_log_trace_pow (hA : A.IsHermitian) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 1 ≤ A i i) (hρ : 0 < pfRoot A) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * Real.log (A ^ M).trace) atTop
      (𝓝 (Real.log (pfRoot A))) := by
  have hC : 0 < min 1 (pfRoot A)⁻¹ := by positivity
  have hD : (0 : ℝ) < Fintype.card ι := by positivity
  refine (tendsto_scaled_log_mul_pow hC hρ).squeeze (tendsto_scaled_log_mul_pow hD hρ) ?_ ?_
  · intro M
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (mul_pos hC (pow_pos hρ _))
      (trace_pow_lower hA hnn hd hρ M)) (by positivity)
  · intro M
    have hp := (mul_pos hC (pow_pos hρ M)).trans_le (trace_pow_lower hA hnn hd hρ M)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hp
      (trace_pow_le_card_mul_pfRoot_pow hA hnn M)) (by positivity)

end PottsDiscontinuity.PerronFrobenius
