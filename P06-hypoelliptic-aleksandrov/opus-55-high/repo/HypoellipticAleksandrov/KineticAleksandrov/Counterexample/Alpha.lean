module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Subcritical homogeneity exponent

Appendix C: choose the exponent before fixing the profile and coefficients.
-/

public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Every exponent below the kinetic threshold admits a positive source-decay exponent. -/
theorem exists_subcritical_alpha (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < alpha - 2 + 4 * (d : ℝ) / p := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hratio : 1 < 4 * d / p := (lt_div_iff₀ hp0).2 (by simp_all)
  have hratio0 : 0 < 4 * d / p := div_pos (by positivity) hp0
  obtain ⟨alpha, ha, ha1⟩ := exists_between
    (show max _ (2 - 4 * d / p) < 1 from
      max_lt zero_lt_one (by linarith))
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
