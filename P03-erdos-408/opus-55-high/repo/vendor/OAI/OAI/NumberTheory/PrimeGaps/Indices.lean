module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

namespace OAI

namespace LargePrimeGaps

noncomputable def theta (n : ℕ) : ℝ := if Nat.Prime n then Real.log n else 0

theorem log_pos_of_two_le {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log (X : ℝ) :=
  Real.log_pos (by exact_mod_cast (by omega))

theorem theta_nonneg (n : ℕ) : 0 ≤ theta n := by
  by_cases hn : Nat.Prime n
  · simp only [theta, ite_eq_left hn]
    positivity
  · simp [theta, hn]


end LargePrimeGaps

end OAI
