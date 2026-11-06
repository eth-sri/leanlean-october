module

public import PottsDiscontinuity.Bethe.AsymptoticTaylor

/-! # The averaged Taylor expansion, uniform in both offset parities -/

public section

open Set
open scoped BigOperators

namespace PottsDiscontinuity.Bethe

theorem abs_average_four_le {a b c d R : ℝ}
    (ha : |a| ≤ R) (hb : |b| ≤ R) (hc : |c| ≤ R) (hd : |d| ≤ R) :
    |(a + b + c + d) / 4| ≤ R := by
  grind

theorem theta_sum_mean_remainder {Δ : ℝ} (hΔ : Δ < -1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N n : ℕ), 0 < N → n ≤ N →
      ∀ (x x₀ x₁ : ℝ) (y y₀ y₁ : Fin n → ℝ),
      x ∈ Icc (-Real.pi) Real.pi → x₀ ∈ Icc (-Real.pi) Real.pi → x₁ ∈ Icc (-Real.pi) Real.pi →
      (∀ j, y j ∈ Icc (-Real.pi) Real.pi) →
      (∀ j, y₀ j ∈ Icc (-Real.pi) Real.pi) → (∀ j, y₁ j ∈ Icc (-Real.pi) Real.pi) →
      ∀ B : ℝ, 0 ≤ B → |x₀ - x| ≤ B / N → |x₁ - x| ≤ B / N →
      (∀ j, |y₀ j - y j| ≤ B / N) → (∀ j, |y₁ j - y j| ≤ B / N) →
      |(∑ j, ((theta Δ x₀ (y₀ j) + theta Δ x₀ (y₁ j) +
          theta Δ x₁ (y₀ j) + theta Δ x₁ (y₁ j)) / 4 - theta Δ x (y j))) -
        (∑ j, d1Theta Δ x (y j)) * ((x₀ + x₁) / 2 - x) -
        ∑ j, d2Theta Δ x (y j) * ((y₀ j + y₁ j) / 2 - y j)| ≤ K * B ^ 2 / N := by
  obtain ⟨K, hK, hTaylor⟩ := theta_sum_linearized_remainder hΔ
  refine ⟨K, hK, ?_⟩
  intro N n hN hn x x₀ x₁ y y₀ y₁ hx hx₀ hx₁ hy hy₀ hy₁ B hB h₀ h₁ hy₀B hy₁B
  have hb := abs_average_four_le (hTaylor N n hN hn x x₀ y y₀ hx hx₀ hy hy₀ B hB h₀ hy₀B) (hTaylor N n hN hn x x₀ y y₁ hx hx₀ hy hy₁ B hB h₀ hy₁B) (hTaylor N n hN hn x x₁ y y₀ hx hx₁ hy hy₀ B hB h₁ hy₀B) (hTaylor N n hN hn x x₁ y y₁ hx hx₁ hy hy₁ B hB h₁ hy₁B)
  have hmean : (∑ j, d2Theta Δ x (y j) * ((y₀ j + y₁ j) / 2 - y j)) =
      ((∑ j, d2Theta Δ x (y j) * (y₀ j - y j)) +
        ∑ j, d2Theta Δ x (y j) * (y₁ j - y j)) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    grind
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib] at hb ⊢
  grind

end PottsDiscontinuity.Bethe
