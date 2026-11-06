module
import Mathlib
public import MathCollab.Density.FixedDetectorCover

@[expose] public section

open Complex Filter
open scoped BigOperators Topology
noncomputable section
namespace MathCollab.Density







/- Direct divisor-power domination of genuine Dirichlet convolution powers.
For k<=4 this gives exponent <=8 and the required uniform subpower bound. -/
theorem arithmeticFunction_pow_norm_le {f : ArithmeticFunction ℂ}
    (hf : ∀ n : ℕ, ‖f n‖ ≤ (n.divisors.card : ℝ)) (k n : ℕ) :
    ‖(f^k) n‖ ≤ (n.divisors.card : ℝ)^(2*k) := by
  induction k generalizing n with
  | zero => simp only [pow_zero, ArithmeticFunction.one_apply, mul_zero]; split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply]
    have hb : ∀ p ∈ n.divisorsAntidiagonal,
        ‖(f^k) p.1*f p.2‖ ≤ (n.divisors.card : ℝ)^(2*k+1) := by
      intro p hp
      obtain ⟨he, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      have hd1 : p.1 ∣ n := ⟨p.2, he.symm⟩
      have hd2 : p.2 ∣ n := ⟨p.1, by rw [mul_comm]; exact he.symm⟩
      have hc1 : (p.1.divisors.card : ℝ) ≤ n.divisors.card := by
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn hd1)
      have hc2 : (p.2.divisors.card : ℝ) ≤ n.divisors.card := by
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn hd2)
      rw [norm_mul, pow_succ]
      exact mul_le_mul ((ih p.1).trans (pow_le_pow_left₀ (by positivity) hc1 _))
        ((hf p.2).trans hc2) (norm_nonneg _) (by positivity)
    calc
      _ ≤ ∑ p ∈ n.divisorsAntidiagonal, ‖(f^k) p.1*f p.2‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (n.divisors.card : ℝ)^(2*k+1) := Finset.sum_le_sum hb
      _ = _ := by
        rw [Finset.sum_const, ← Nat.map_div_right_divisors, Finset.card_map, nsmul_eq_mul]
        ring










