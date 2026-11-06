module

public import NearlyMinimax.ScoreCostAlgebra
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗎

/-! Actual exponential-series tails used to sum the local score energies. -/

def poissonCountWeight (x : ℝ) (k : ℕ) : ℝ := x ^ k / 𝖽₁

theorem poissonCountWeight_nonneg (hx : 0 ≤ x) k :
    0 ≤ poissonCountWeight x k := by unfold poissonCountWeight; positivity

theorem poissonCountWeight_summable x : Summable $ poissonCountWeight x :=
  Real.summable_pow_div_factorial x

theorem poissonCountWeight_tsum x :
     ∑' k, poissonCountWeight x k = Real.exp x := by
  simpa only [poissonCountWeight, Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp x).tsum_eq

𝗇 𝔄 a + j
𝗇 𝔅 poissonCountWeight x a * poissonCountWeight x j
theorem poissonCountWeight_add_le (hx : 0 ≤ x) a j :
    poissonCountWeight x 𝔄 ≤ 𝔅 := by
  have hf : a.factorial * j.factorial ≤ ((𝔄).factorial : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) $ Nat.factorial_mul_factorial_dvd_factorial_add a j
  have h := div_le_div_of_nonneg_left (pow_nonneg hx 𝔄)
    (mul_pos (by exact_mod_cast Nat.factorial_pos a) $ by exact_mod_cast Nat.factorial_pos j ) hf
  simpa only [poissonCountWeight, pow_add, div_mul_div_comm] using h

theorem poissonCountWeight_tail_le (hx : 0 ≤ x) a :
     ∑' j, poissonCountWeight x 𝔄 ≤ Real.exp x * poissonCountWeight x a := by
  have hs : Summable fun j => poissonCountWeight x 𝔄 :=
    (poissonCountWeight_summable x).comp_injective fun _ _ h => Nat.add_left_cancel h
  calc
    _ ≤ ∑' j, 𝔅 :=
      hs.tsum_le_tsum (poissonCountWeight_add_le hx a) $ (poissonCountWeight_summable x).mul_left _
    _ = Real.exp x * poissonCountWeight x a := by
      rw [tsum_mul_left, poissonCountWeight_tsum, mul_comm]
