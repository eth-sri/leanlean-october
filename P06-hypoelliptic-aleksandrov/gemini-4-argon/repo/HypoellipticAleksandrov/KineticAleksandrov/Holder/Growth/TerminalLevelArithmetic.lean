module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.ParameterChoice
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Exact scalar induction and leakage choice for the source density ladder -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

open scoped BigOperators

/- The power sum has the shifted recurrence used in the density ladder. -/
theorem ladder_power_sum_succ (q : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), q ^ k) =
      q * (∑ k ∈ Finset.range n, q ^ k) + 1 := by
  rw [Finset.sum_range_succ']
  simp only [pow_succ, pow_zero]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/- The exact source ladder gives its terminal-level lower bound by numeric induction. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
