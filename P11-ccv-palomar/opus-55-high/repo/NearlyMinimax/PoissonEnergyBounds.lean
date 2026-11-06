module

public import NearlyMinimax.FactorialSeriesTail
public import RoughRegime.Macro
public import Mathlib.Data.Nat.Choose.Bounds
public import RoughRegime.Notation

𝗍

/-! Binomial count energies are bounded by the actual factorial-weighted
series. Geometric full-response bounds prove that the series is finite. -/
𝚨

theorem polynomial_count_factor_le (k r : ℕ) :
    k ^ r ≤ (𝙉 ^ r) ^ k := by
  have hk : k ≤ 𝙉 ^ k := by exact_mod_cast (Nat.lt_two_pow_self ).le
  simpa only [← pow_mul, Nat.mul_comm] using pow_le_pow_left₀ (Nat.cast_nonneg k) hk r
