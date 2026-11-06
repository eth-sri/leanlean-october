module
public import GuthMaynard.Improvement.UpperWindowBudgets
public import GuthMaynard.Improvement.UpperCurveLargeValues

public section

open Finset
namespace GuthMaynard.Improvement

/-- Actual large values for sigma in [5/7,3/4]. The intermediate lengths
pad the observation time to N^(6/5), preserving the original threshold and
finite set. The middle theorem is invoked only within its proved range. -/
theorem upper_window_large_values {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/100) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ H N t₀ : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
      5/7 ≤ σ → σ ≤ 3/4 → 2 ≤ H → 2 ≤ N →
      H^(3/4:ℝ) ≤ N → N ≤ H^(9/8+δ) →
      (∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) →
      (∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+H) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, N^σ*H^(-2*δ) ≤ ‖boundedPolynomial N a t‖) →
      (W.card:ℝ) ≤ C*H^((39/17)*(1-σ)+10*δ) := by pf_4 upper_window_length_budgets 39 17 (7/8:ℝ) upper_window_padded_time upper_window_mean_budget

end GuthMaynard.Improvement
