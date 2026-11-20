module

public import NearlyMinimax.GridMixtureRisk


@[expose] public section

/-! # The actual nonparametric low-smoothness lower bound

A concrete globally Hölder tent-window prior supplies admissible states in
original Model, its complete sample probability experiment, and a derived
score budget. Numeric grid rounding gives the paper's nonparametric rate.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false

/-- The nonparametric low-smoothness minimax lower bound for all sample sizes
n≥1, proved in the original regression experiment without a rate premise. -/
theorem low_smoothness_nonparametric_minimax_lower {d : ℕ} {C : ModelConstants d}
    (hs1 : C.smoothness ≤ 1) (hd : 4 * C.smoothness ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * n ^ (-4 * C.smoothness / (d + 4 * C.smoothness))) ≤
        minimaxRMS C n := by
  obtain ⟨G⟩ := lowSmoothnessPriorConstants_exists C
  refine ⟨G.b ^ 2 / (3 * 5 ^ (2 * C.smoothness)),
    div_pos (pow_pos G.b_pos 2) (mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _)), ?_⟩
  intro n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let k := lowSmoothnessGrid d C.smoothness n
  let η := lowSmoothnessAmplitude d C.smoothness G.b n
  have hk : 1 ≤ k := by
    bound [lowSmoothnessGrid_ge_four (d := d) C.smoothness_pos hnR]
  have hg := lowSmoothness_amplitude_legal_guards C.smoothness_pos G.b_pos.le hnR
    G.field_guard G.variance_guard
  have hη  := hg.1
  have hfield  := hg.2.1
  have hvariance  := hg.2.2
  have hmean  :=
    lowSmoothness_design_occupancy C.smoothness_pos hd hnR
  have hbudget : gridUniformScoreBudget G.ternary k n η ≤ 1 := by
    have hb := (mul_le_mul_of_nonneg_left
        (lowSmoothness_numeric_score_budget C.smoothness_pos G.b_pos.le hnR)
        (lowSmoothnessScoreConstant_nonneg G.ternary) : lowSmoothnessScoreConstant G.ternary *
        (↑n ^ 2 * lowSmoothnessAmplitude d C.smoothness G.b ↑n ^ 4 / ↑(lowSmoothnessGrid d C.smoothness ↑n) ^ d)
        ≤ lowSmoothnessScoreConstant G.ternary * G.b ^ 4)
    have he : gridUniformScoreBudget G.ternary k n η =
        lowSmoothnessScoreConstant G.ternary *
          (n ^ 2 * (η) ^ 4 /
            (k) ^ d) := by
      simp [gridUniformScoreBudget, lowSmoothnessScoreConstant] <;> ring
    rw [he]
    exact hb.trans G.score_guard
  apply (ENNReal.ofReal_le_ofReal ?_).trans (grid_prior_minimax_lower hk hs1 G.b_pos.le hη hfield hvariance (rfl) G.holder_guard hmean hbudget)
  calc
    _ = _ := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (lowSmoothness_variance_separation (d := d) (b := G.b) C.smoothness_pos hnR) (by norm_num)

end NearlyMinimax
