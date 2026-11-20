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
variable {d n : ℕ} (C : ModelConstants d)

private theorem lowSmoothnessScale_eq_ite (hn : 1 ≤ n) :
    lowSmoothnessScale C.smoothness d n = if (d : ℝ) ≤ 4 * C.smoothness then
      (n : ℝ) ^ (-(1 / 2 : ℝ)) else (n : ℝ) ^ (-(4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness))) := by
  unfold lowSmoothnessScale
  have hden : 0 < (d : ℝ) + 4 * C.smoothness := by have := C.smoothness_pos; positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  split_ifs with hd
  · apply max_eq_left (Real.rpow_le_rpow_of_exponent_le hn' ?_)
    rw [neg_le_neg_iff, le_div_iff₀ hden]
    linarith
  · apply max_eq_right (Real.rpow_le_rpow_of_exponent_le hn' ?_)
    rw [neg_le_neg_iff, div_le_iff₀ hden]
    linarith

end

section
variable {d : ℕ} (C : ModelConstants d)

/-- A genuine lower bound for the maximum of the two low-smoothness rates,
including the critical dimension and n = 1. -/
theorem low_smoothness_max_minimax_lower
    (hs : C.smoothness ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ENNReal.ofReal (c * lowSmoothnessScale C.smoothness d n) ≤ minimaxRMS C n := by
  by_cases hd : (d : ℝ) ≤ 4 * C.smoothness
  · obtain ⟨c, hc, hbound⟩ := parametric_minimax_lower C
    refine ⟨c, hc, ?_⟩
    intro n hn
    simpa only [lowSmoothnessScale_eq_ite C hn, if_pos hd] using hbound n hn
  · obtain ⟨c, hc, hbound⟩ := low_smoothness_nonparametric_minimax_lower C hs (le_of_not_ge hd)
    refine ⟨c, hc, ?_⟩
    intro n hn
    simpa only [lowSmoothnessScale_eq_ite C hn, if_neg hd, neg_div, neg_mul] using hbound n hn

/-- Manuscript `thm:main2`: both bounds hold for the original statistical
class, with one positive constant for every sample size n ≥ 1. -/
theorem paper_low_smoothness : LowSmoothnessClaim C := by
  intro hs
  obtain ⟨c, hc, hbound⟩ := low_smoothness_max_minimax_lower C hs
  refine uniform_rms_bracket C _ (B := elementaryRMSConstant C) (fun _ => by unfold lowSmoothnessScale; positivity) hc hbound ?_
  intro n hn
  have hupper := (ENNReal.rpow_le_rpow
      (minimaxRisk_le_worstCaseRisk C (elementaryEstimator C n)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
    (elementary_upper_low_smoothness C hs (by omega : 0 < n))
  simpa only [minimaxRMS, lowSmoothnessScale, neg_mul, neg_div] using hupper

end

end NearlyMinimax
