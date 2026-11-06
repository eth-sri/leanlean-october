module

public import NearlyMinimax.FactorialSeriesTail
public import RoughRegime.Macro
public import Mathlib.Analysis.SpecificLimits.Basic
public import RoughRegime.Notation

𝗍

/-! Finite geometric summation of the actual higher-target row activity bounds.
The estimate preserves the leading exp(tau_M * M) activity factor. -/
𝚪
𝚨

theorem finite_geometric_tail_le_two_mul {q : ℝ} (hq : 0 ≤ q) (hqh : q ≤ 𝙖)
    m : ∑ j ∈ Finset.range m, q ^ 𝘑₁ ≤ 2 * q := by
  calc
    _ = q * ∑ j ∈ Finset.range m, q ^ j := by simp_rw [pow_succ]; rw [Finset.mul_sum]; ring
    _ ≤ q * ∑ j ∈ Finset.range m, 𝙖 ^ j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hq hqh j) hq
    _ ≤ q * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le m) hq
    𝘿 := mul_comm ..
