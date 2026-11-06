module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic

/-! # Bounded supremum iteration with a geometrically growing error

This is the elementary iteration step in the return-time proof.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Filter Finset
open scoped Topology

/- Iterated substitution in a nonnegative-coefficient recurrence. -/
theorem return_recurrence_substitution (f : ℕ → ℝ) (q r B )
    (hq : 0 ≤ q) (hstep : ∀ n, f n ≤ q * f (n + 1) + B * r ^ n)
    (n N : ℕ) :
    f n ≤ q ^ N * f (n + N) + B * r ^ n * ∑ j ∈ range N, (q * r) ^ j := by
  induction N generalizing n with
  | zero => simp
  | succ N ih =>
    have htail := mul_le_mul_of_nonneg_left (ih (n + 1)) hq
    apply (hstep n).trans
    apply (add_le_add htail (le_refl (B * r ^ n))).trans_eq
    rw [geom_sum_succ, pow_succ]
    simp only [pow_succ]
    have hindex : n + 1 + N = n + (N + 1) := by omega
    rw [hindex]
    ring

/- A bounded sequence loses the terminal supremum when the absorption ratio is small. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
