module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace NearlyMinimax

section
variable {n : ℕ} {f : (Fin n → Fin 3) → ℝ} {b : ℝ}

/-- A uniform bound over response words costs their cardinality. -/
theorem ternary_sum_le (h : ∀ y, f y ≤ b) :
    (∑ y, f y) ≤ (3 : ℝ)^n * b := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using Finset.sum_le_sum (s := Finset.univ) (fun y _ => h y)

theorem ternary_sum_sq_le (h : ∀ y, |f y| ≤ b) :
    (∑ y, f y ^ 2) ≤ (3 : ℝ)^n * b ^ 2 :=
  ternary_sum_le fun y => by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h y) 2

end

end NearlyMinimax
