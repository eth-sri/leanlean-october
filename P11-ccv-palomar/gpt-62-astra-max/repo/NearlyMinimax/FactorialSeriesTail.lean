module

public import NearlyMinimax.ScoreCostAlgebra
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section

/-! Actual exponential-series tails used to sum the local score energies. -/
noncomputable section
namespace NearlyMinimax

def poissonCountWeight (x : ℝ) (k : ℕ) : ℝ := x ^ k / k.factorial

variable {x : ℝ} (hx : 0 ≤ x) (a : ℕ)

include hx in
theorem poissonCountWeight_nonneg (k : ℕ) :
    0 ≤ poissonCountWeight x k := by unfold poissonCountWeight; positivity

theorem poissonCountWeight_summable (x : ℝ) : Summable (poissonCountWeight x) :=
  Real.summable_pow_div_factorial x

theorem poissonCountWeight_tsum (x : ℝ) :
    (∑' k, poissonCountWeight x k) = Real.exp x := by
  simpa only [poissonCountWeight, Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq

include hx in
theorem poissonCountWeight_add_le (j : ℕ) :
    poissonCountWeight x (a + j) ≤ poissonCountWeight x a * poissonCountWeight x j := by
  have hfNat  :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add a j)
  simpa only [poissonCountWeight, pow_add, div_mul_div_comm] using div_le_div_of_nonneg_left (pow_nonneg hx (a + j)) (by positivity) (by
    exact_mod_cast hfNat)

include hx in
theorem poissonCountWeight_tail_le :
    (∑' j, poissonCountWeight x (a + j)) ≤ Real.exp x * poissonCountWeight x a := by
  calc
    _ ≤ _ :=
      ((poissonCountWeight_summable x).comp_injective (fun _ _ h => Nat.add_left_cancel h)).tsum_le_tsum (poissonCountWeight_add_le hx a) ((poissonCountWeight_summable x).mul_left _)
    _ = _ := by
      rw [tsum_mul_left, poissonCountWeight_tsum, mul_comm]

end NearlyMinimax
