module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TimePowerCount
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionVisitsStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.DegreeGap
import Mathlib.Tactic

/-! # Summation of the combined time and position decay

Source: companion paper, (8.30). This is the numeric summation step; it makes no
assertion that the canonical visit masses satisfy the required decay.
-/

public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open scoped BigOperators

/-- The admissible barrier degree gives the source range `1 < gamma < 2`. -/
theorem enlargedAdmissibleAlpha_gamma_range {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : enlargedAdmissibleAlpha lam Lam hlam hLam alpha) :
    1 < 2 - alpha ∧ 2 - alpha < 2 := by
  have hb := bellmanAdjointExponent_two_le (Lam / lam) ((le_div_iff₀ hlam).2
    (by simp_all))
  obtain ⟨hal, hau⟩ := ha
  grind

/-- The combined decay exponent is summable up to the source horizon power. -/
theorem position_decay_power_sum_horizon_le (g q : ℝ)
    (hg : 1 < g ∧ g < 2) (hq : 1 < q ∧ q < 3 / 2)
    (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (N : ℕ)
    (hN : (N : ℝ) ≤ 2 + (R / r) ^ 2) :
    (∑ j ∈ Finset.range (N + 1),
      (1 + (j : ℝ)) ^ (-(1 + g * (q - 1)) / 2)) ≤
      ((1 + 1 / (1 - (1 + g * (q - 1)) / 2)) *
        (3 : ℝ) ^ (1 - (1 + g * (q - 1)) / 2)) *
          (1 + R / r) ^ (1 - g * (q - 1)) := by
  have hprod : 0 < g * (q - 1) := mul_pos (by linarith) (by simp_all)
  have hprod1 : g * (q - 1) < 1 := by
    have h := mul_lt_mul_of_pos_right hg.2 (by simp_all : 0 < q - 1)
    linarith
  have hs := time_decay_power_sum_horizon_le (1 + g * (q - 1))
    (by linarith) (by linarith) R r hR hr N hN
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
