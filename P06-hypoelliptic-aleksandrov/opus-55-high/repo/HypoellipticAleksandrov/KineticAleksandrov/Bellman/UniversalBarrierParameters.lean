module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.DegreeGap
import Mathlib.Tactic

/-! # The permitted barrier interval and the occupation exponent arithmetic -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The source interval implies positivity and places the radial pair above the adjoint exponent. -/
theorem bellman_barrier_parameter_range (lam Lam : ℝ) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simp_all) - 2 < alpha)
    (ha1 : alpha < 1) :
    0 < alpha ∧ alpha < 1 ∧
      bellmanAdjointExponent (Lam / lam)
        (by grind) < 2 + alpha := by
  have ht := bellmanAdjointExponent_two_le (Lam / lam)
    (by grind)
  grind

end HypoellipticAleksandrov.KineticAleksandrov
