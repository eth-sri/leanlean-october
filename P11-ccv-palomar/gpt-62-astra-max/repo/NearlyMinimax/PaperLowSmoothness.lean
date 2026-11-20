module

public import NearlyMinimax.ElementaryUpper
public import NearlyMinimax.LowSmoothnessLower
public import NearlyMinimax.ParametricLower
public import NearlyMinimax.PaperGoals


@[expose] public section

/-! The complete all-sample-size low-smoothness minimax bracket from the
constructed pair estimator and the actual ternary submodels. -/
noncomputable section
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

section
variable {d n : ℕ} {C : ModelConstants d}

theorem lowSmoothnessScale_eq_root
    (hd : d ≤ 4 * C.smoothness) (hn : 1 ≤ n) :
    lowSmoothnessScale C.smoothness d n = n ^ (-(1 / 2 : ℝ)) := by
  have hexp : -(4 * C.smoothness / (d + 4 * C.smoothness)) ≤
      -(1 / 2) := by
    apply neg_le_neg
    apply (le_div_iff₀ (by
      linarith [C.smoothness_pos])).mpr
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n) hexp
  exact max_eq_left hpow

theorem lowSmoothnessScale_eq_nonparametric
    (hd : 4 * C.smoothness ≤ d) (hn : 1 ≤ n) :
    lowSmoothnessScale C.smoothness d n =
      n ^ (-4 * C.smoothness / (d + 4 * C.smoothness)) := by
  have hexp : -(1 / 2) ≤ -(4 * C.smoothness / (d + 4 * C.smoothness)) := by
    apply neg_le_neg
    apply (div_le_iff₀ (by
      linarith [C.smoothness_pos])).mpr
    nlinarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n) hexp
  have he : -(4 * C.smoothness / (d + 4 * C.smoothness)) =
      -4 * C.smoothness / (d + 4 * C.smoothness) := by ring
  simpa only [lowSmoothnessScale, he] using max_eq_right hpow

end

/-- A genuine lower bound for the maximum of the two low-smoothness rates,
including the critical dimension and n = 1. -/
theorem low_smoothness_max_minimax_lower {d : ℕ} {C : ModelConstants d}
    (hs : C.smoothness ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, 1 ≤ n →
      ENNReal.ofReal (c * lowSmoothnessScale C.smoothness d n) ≤ minimaxRMS C n := by
  by_cases hd : d ≤ 4 * C.smoothness
  · obtain ⟨c, hc, hbound⟩ := parametric_minimax_lower C
    refine ⟨c, hc, ?_⟩
    intro n hn
    rw [lowSmoothnessScale_eq_root hd hn]
    exact hbound n hn
  · obtain ⟨c, hc, hbound⟩ := low_smoothness_nonparametric_minimax_lower hs (le_of_not_ge hd)
    refine ⟨c, hc, ?_⟩
    intro n hn
    rw [lowSmoothnessScale_eq_nonparametric (le_of_not_ge hd) hn]
    exact hbound n hn

end NearlyMinimax
