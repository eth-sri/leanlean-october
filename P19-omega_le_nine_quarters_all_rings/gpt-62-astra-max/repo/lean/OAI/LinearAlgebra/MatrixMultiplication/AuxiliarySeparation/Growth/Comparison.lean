module

public import Mathlib

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.AuxiliarySeparation
open Polynomial Filter
open scoped Topology Polynomial

/-- No polynomial prefactor survives at the exponential scale. -/
theorem polynomial_overhead {a b : ℝ} (ha : 0 ≤ a) (p : ℝ[X])
    (h : ∀ n : ℕ, b^n ≤ p.eval (n:ℝ) * a^n) : b ≤ a := by
  by_contra! hab
  have hb := ha.trans_lt hab
  have hr := (div_lt_one hb).mpr hab
  have lim : Tendsto (fun n : ℕ => p.eval (n:ℝ) * (a/b)^n) atTop (𝓝 0) := by
    clear h
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa [add_mul] using hp.add hq
    | monomial i c => simpa [mul_assoc] using
        (tendsto_pow_const_mul_const_pow_of_lt_one i (div_nonneg ha hb.le) hr).const_mul c
  have bad := ge_of_tendsto lim (Eventually.of_forall fun n =>
    (show (1:ℝ) ≤ _ from by simp_all [div_pow, ← mul_div_assoc, one_le_div₀ (pow_pos hb n)]))
  grind

/-- A uniform bound on all positive natural inputs forces the exponent on
the left to be no larger than the exponent on the right. -/
theorem rpow_exponent_le_of_nat_bound {a b C : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ a ≤ C * (n : ℝ) ^ b) :
    a ≤ b := by
  apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp
  apply polynomial_overhead (by positivity) (Polynomial.C C)
  intro k
  simpa [Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2)] using
    hbound (2^k) (by grind)

private theorem compare_at_two (f g : ℕ →*o ℝ)
    (he : f 2 = g 2) {n : ℕ} (hn : 0 < n) : f n ≤ g n := by
  have hp {i : ℕ} (hi : 0 < i) : 0 ≤ g i := by
    exact zero_le_one.trans (by simpa using g.monotone' (show 1 ≤ i from hi))
  apply polynomial_overhead (hp hn) (Polynomial.C (g 2))
  intro k
  obtain ⟨m, hl, hu⟩ := exists_nat_pow_near (Nat.one_le_pow _ _ hn) (by decide : 1 < (2:ℕ))
  simpa [he] using (f.monotone' hu.le).trans (show f (2^(m+1)) ≤ g 2 * g (n^k) by
    rw [pow_succ', map_mul, map_pow, he, ← map_pow]; exact mul_le_mul_of_nonneg_left (g.monotone' hl) (hp (by decide)))

theorem nat_price (f : ℕ →*o ℝ) (h : f 2 = 2) {n : ℕ} (hn : 0 < n) : f n = n := by
  let g : ℕ →*o ℝ := { Nat.castRingHom ℝ with monotone' := Nat.mono_cast }
  exact le_antisymm (compare_at_two f g h hn) (compare_at_two g f h.symm hn)

end OAI.MatrixMultiplication.AuxiliarySeparation
