module

public import NearlyMinimax.FactorialSeriesTail
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Finite geometric summation of the actual higher-target row activity bounds.
The estimate preserves the leading exp(tau_M * M) activity factor. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax

theorem finite_geometric_tail_le_two_mul {q : ℝ} (hq : 0 ≤ q) (hqh : q ≤ 1 / 2)
    (m : ℕ) : (∑ j ∈ Finset.range m, q ^ (j + 1)) ≤ 2 * q := by
  calc
    _ = q * ∑ j ∈ Finset.range m, q ^ j := by simp_rw [pow_succ]; rw [Finset.mul_sum]; ring
    _ ≤ q * ∑ j ∈ Finset.range m, (1 / (2 : ℝ)) ^ j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hq hqh j) hq
    _ ≤ q * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le m) hq
    _ = _ := mul_comm _ _

end NearlyMinimax
