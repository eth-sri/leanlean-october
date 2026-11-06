module

public import NearlyMinimax.FactorialSeriesTail
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-! Binomial count energies are bounded by the actual factorial-weighted
series. Geometric full-response bounds prove that the series is finite. -/
noncomputable section
namespace NearlyMinimax

theorem polynomial_count_factor_le (k r : ℕ) :
    (k : ℝ) ^ r ≤ (2 ^ r) ^ k := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h := pow_le_pow_left₀ (Nat.cast_nonneg k) hk r
  simpa only [← pow_mul, Nat.mul_comm] using h

end NearlyMinimax
